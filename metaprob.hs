{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}

import Control.Monad.Random

--
-- METAPROB
--

-- This code consists of two sections.
--
-- In the first, we declare the INTERFACE that distributions and
-- traces are expected to satisfy.  In terms of these data, we define
-- generative functions, some transformations among them, and the
-- meta-circular evaluator.
--
-- In the second, we give EXAMPLES of an implementation of traces and
-- two implementations of distributions, one measure-theoretic and one
-- sampler-theoretic, and some computations.

-- TODOS:
--   * Probabilistic programs of type "A -> B";
--     currently just type A ~= "() -> A" is supported
--   * Some notion of continuous distributions


--
-- INTERFACE
--

-- Here is some of our notation compared with the Metaprob paper:
--   * The space K of trace keys is represented by `key`.
--   * The type A of elements we wish to compute about is `a`.
--   * We fix some parametric type f(A) in the world of the paper.
--     * Key examples: f(A) = A, and f(A) = A x Trace.
-- The rest of the correspondence is documented as we go.

-- Describes distributions R(f(A)) on elements f(A)
class Distr distr elt | distr -> elt where
  dirac :: elt a -> distr a
  convolve :: Eq (elt a) => distr a -> (elt a -> distr a) -> distr a

-- Defines generative functions P(f(A)) in terms of f(A) and R(f(A))
data GenFn key distr elt a =
  Sample key (distr a) (elt a -> Double) |
  Ret (elt a) |
  Semicolon (GenFn key distr elt a) (elt a -> GenFn key distr elt a)

-- Defines the "Gen" interpretation [[ ]]_g from P(f(A)) to R(f(A))
runGen :: (Distr distr elt, Eq (elt a)) =>
          GenFn key distr elt a -> distr a
runGen (Sample k sample score) = sample
runGen (Ret e) = dirac e
runGen (Semicolon p1 p2) = convolve (runGen p1) (runGen . p2)

data TValue a = TNone | Traced a | Intervene a | Observe a
                deriving (Eq, Show)
-- In the context of `class Trace`,
--   * `elt a` corresponds to f(A) = A,
--   * `traced a` corresponds to f(A) = A x Trace, and
--   * `wtraced a` corresponds to f(A) = A x Trace x R^+.
-- And, yes, `trace` corresponds to Trace.
class Trace trace key elt traced wtraced |
      trace -> key elt traced wtraced,
      traced -> trace, wtraced -> traced where
  getTrace :: trace a -> [(key, TValue (elt a))]
  emptyTrace :: trace a
  kvTrace :: key -> TValue (elt a) -> trace a
  appendTrace :: trace a -> trace a -> trace a
  getTraced :: traced a -> (elt a, trace a)
  makeTraced :: (elt a, trace a) -> traced a
  getWTraced :: wtraced a -> (elt a, trace a, Double)
  makeWTraced :: (elt a, trace a, Double) -> wtraced a
traceValue :: (Trace trace key elt traced wtraced, Eq key) =>
              trace a -> key -> TValue (elt a)
traceValue t k = let res = filter ((== k) . fst) (getTrace t) in
                 if null res then TNone else snd $ head res
extendByZero :: Trace trace key elt traced wtraced =>
                (elt a -> Double) -> traced a -> Double
extendByZero f xt = let (x, t) = getTraced xt in
                    if null $ getTrace t then f x else 0.0
extendByZeroW :: Trace trace key elt traced wtraced =>
                 (elt a -> Double) -> wtraced a -> Double
extendByZeroW f xtw = let (x, t, _) = getWTraced xtw in
                      if null $ getTrace t then f x else 0.0

-- Relates R(A) to R(A x Trace) and R(A x Trace x R^+)
class TDistr distr tdistr wtdistr |
      distr -> wtdistr tdistr where
  pushForward :: distr a -> tdistr a
  pushForwardW :: distr a -> wtdistr a

-- Then P(A x Tracing) is `GenFn key tdistr traced a` and
-- P(A x Tracing x R^+) is `GenFn key wtdistr wtraced a`,
-- and we may use the next two functions to make elements of them.

-- Defines the transformation tracing from P(A) to P(A x Tracing)
tracing :: (Trace trace key elt traced wtraced,
            TDistr distr tdistr wtdistr) =>
           GenFn key distr elt a ->
           GenFn key tdistr traced a
tracing (Sample k dist score) =
  Semicolon
    (Sample k (pushForward dist) (extendByZero score))
    (\xt -> let (x, _) = getTraced xt in
            Ret $ makeTraced (x, kvTrace k (Traced x)))
tracing (Ret x) = Ret $ makeTraced (x, emptyTrace)
tracing (Semicolon p1 p2) =
  Semicolon
    (tracing p1)
    (\xs -> let (x, s) = getTraced xs in
            Semicolon
              (tracing (p2 x))
              (\yt -> let (y, t) = getTraced yt in
                      Ret $ makeTraced (y, appendTrace s t)))

-- Defines infer_t from P(A) to P(A x Tracing x R^+)
infer :: (Trace trace key elt traced wtraced,
          TDistr distr tdistr wtdistr,
          Eq key) =>
         trace a -> GenFn key distr elt a ->
         GenFn key wtdistr wtraced a
infer tr (Sample k dist score) =
  Semicolon
    (case traceValue tr k of
       Observe x -> Ret $ makeWTraced (x, emptyTrace, score x)
       Intervene x -> Ret $ makeWTraced (x, emptyTrace, 1.0)
       _ ->
         Semicolon
           (Sample k (pushForwardW dist) (extendByZeroW score))
           (\xtw -> let (x, _, _) = getWTraced xtw in
                    Ret $ makeWTraced (x, emptyTrace, 1.0)))
    (\ytw -> let (y, _, w) = getWTraced ytw in
             Ret $ makeWTraced (y, kvTrace k (Traced y), w))
infer tr (Ret x) = Ret $ makeWTraced (x, emptyTrace, 1.0)
infer tr (Semicolon p1 p2) =
  Semicolon
    (infer tr p1)
    (\xsv -> let (x, s, v) = getWTraced xsv in
             Semicolon
               (infer tr (p2 x))
               (\ytw -> let (y, t, w) = getWTraced ytw in
                        Ret $ makeWTraced
                                (y, appendTrace s t, (v * w))))


--
-- EXAMPLES
--

--
-- Default implementation of shared items
--

data MyElt a = MyElt { myElt :: a } deriving Eq
instance Show a => Show (MyElt a) where
  show (MyElt a) = show a

data MyTrace key a =
  MyTrace { myTrace :: [(key, TValue (MyElt a))] }
  deriving Eq
instance (Show key, Show a) => Show (MyTrace key a) where
  show (MyTrace t) = "Trace " ++ show t

data MyTraced key a =
  MyTraced { myTraced :: (MyElt a, MyTrace key a) }
  deriving Eq
instance (Show key, Show a) => Show (MyTraced key a) where
  show (MyTraced (MyElt x, MyTrace t)) = show (x, t)

data MyWTraced key a =
  MyWTraced { myWTraced :: (MyElt a, MyTrace key a, Double) }
  deriving Eq
instance (Show key, Show a) => Show (MyWTraced key a) where
  show (MyWTraced (MyElt x, MyTrace t, w)) = show (x, t, w)

instance Trace (MyTrace key)
               key
               MyElt
               (MyTraced key)
               (MyWTraced key) where
  getTrace = myTrace
  emptyTrace = MyTrace []
  kvTrace k v = MyTrace [(k, v)]
  appendTrace t1 t2 = MyTrace (myTrace t1 ++ myTrace t2)
  getTraced = myTraced
  makeTraced = MyTraced
  getWTraced = myWTraced
  makeWTraced = MyWTraced

data MySet = Tails | Heads deriving (Show, Eq)
myNot Tails = Heads
myNot Heads = Tails

tObs = MyTrace [(0 :: Int, Observe (MyElt Heads))]
tInt = MyTrace [(0 :: Int, Intervene (MyElt Heads))]


--
-- Example 1:
-- Measure-theoretically, tracking point masses in the support of the
-- distribution
--

squashDiracs :: Eq a => [(a, Double)] -> [(a, Double)]
squashDiracs [] = []
squashDiracs ((x, v) : xvs) =
  let yws = squashDiracs xvs
      hit = filter (\yw -> fst yw == x) yws
      miss = filter (\yw -> fst yw /= x) yws in
  if null hit then (x, v) : yws
              else (x, v + (snd $ head hit)) : miss

data Diracs elt a = Diracs { diracs :: [(elt a, Double)] }
instance Show (elt a) => Show (Diracs elt a) where
  show (Diracs d) = "Diracs" ++ concat (map (\l -> "\n " ++ show l) d)
instance Distr (Diracs elt) elt where
  dirac x = Diracs [(x, 1.0)]
  convolve d1 d2 = Diracs . squashDiracs . concat $
    map (\xu -> let (x, u) = xu in
                map (\yv -> let (y, v) = yv in (y, u * v))
                    (diracs $ d2 x))
        (diracs d1)

instance TDistr (Diracs MyElt)
                (Diracs (MyTraced Int))
                (Diracs (MyWTraced Int)) where
  pushForward (Diracs d) =
    Diracs $ map (\(x, u) -> (makeTraced (x, emptyTrace), u)) d
  pushForwardW (Diracs d)=
    Diracs $ map (\(x, u) -> (makeWTraced (x, emptyTrace, 1.0), u)) d

input1 = Ret $ MyElt Tails
         :: GenFn Int (Diracs MyElt) MyElt MySet
input1a = Sample (0 :: Int)
                 (Diracs [(MyElt Tails, 1.0)])
                 (\(MyElt x) -> if x == Tails then 1.0 else 0.0)
drunkenNot1 k (MyElt x) =
  Sample
    k
    (Diracs [(MyElt $ myNot x, 0.9), (MyElt x, 0.1)])
    (\(MyElt y) ->
       if y == x then 0.1 else if y == myNot x then 0.9 else 0.0)
computed1 =
  Semicolon (Semicolon input1 (drunkenNot1 1)) (drunkenNot1 2)
computed1a =
  Semicolon (Semicolon input1a (drunkenNot1 1)) (drunkenNot1 2)

-- try:
-- runGen computed1
-- runGen computed1a
-- runGen $ tracing computed1
-- runGen $ tracing computed1a
-- runGen $ infer tObs computed1a
-- ...


--
-- Example 2:
-- Executing determinstic sampling prodedures.  This is a conceptual
-- warm-up for Example 3 below.
--

data DSampler elt a = DSampler { sampler :: () -> elt a }
makeDSampler :: elt a -> DSampler elt a
makeDSampler x = DSampler (\_ -> x)
dsample :: DSampler elt a -> elt a
dsample (DSampler s) = s ()
instance Show (elt a) => Show (DSampler elt a) where
  show s = "() -> " ++ show (dsample s)
instance Distr (DSampler elt) elt where
  dirac = makeDSampler
  convolve s1 s2 = s2 $ dsample s1

instance TDistr (DSampler MyElt)
                (DSampler (MyTraced Int))
                (DSampler (MyWTraced Int)) where
  pushForward s =
    makeDSampler $ MyTraced (dsample s, emptyTrace)
  pushForwardW s =
    makeDSampler $ MyWTraced (dsample s, emptyTrace, 1.0)

input2 = Ret $ MyElt Tails
         :: GenFn Int (DSampler MyElt) MyElt MySet
input2a = Sample (0 :: Int)
                 (makeDSampler $ MyElt Tails)
                 (\(MyElt x) -> if x == Tails then 1.0 else 0.0)
-- This is especially not stochastic right now:
drunkenNot2 k (MyElt x) =
  Sample
    k
    (makeDSampler . MyElt $ myNot x)
    (\(MyElt y) ->
       if y == x then 0.1 else if y == myNot x then 0.9 else 0.0)
computed2 =
  Semicolon (Semicolon input2 (drunkenNot2 1)) (drunkenNot2 2)
computed2a =
  Semicolon (Semicolon input2a (drunkenNot2 1)) (drunkenNot2 2)

-- try:
-- runGen computed2
-- runGen computed2a
-- runGen $ tracing computed2
-- runGen $ tracing computed2a
-- runGen $ infer tObs computed2a
-- ...


--
-- Example 3:
-- Executing randomized/stochastic sampling procedures.
--

newtype RSampler g elt a = RSampler { rsampler :: Rand g (elt a) }
-- The presence of `elt a` rather than just `a` means we must rewrap
-- our own versions of `fmap` and `bind`:
eltfmap :: (elt a -> elt' a) ->
           RSampler g elt a ->
           RSampler g elt' a
eltfmap f = RSampler . fmap f . rsampler
eltbind :: RSampler g elt a ->
           (elt a -> RSampler g elt a) ->
           RSampler g elt a
x `eltbind` f = RSampler $ (rsampler x) >>= (\y -> rsampler (f y))

makeRSampler :: RandomGen g => elt a -> RSampler g elt a
makeRSampler x = RSampler $ uniform [x]
-- This plays the role of the Show instance:
rsample :: RSampler StdGen elt a -> IO (elt a)
rsample = evalRandIO . rsampler
instance RandomGen g => Distr (RSampler g elt) elt where
  dirac = makeRSampler
  convolve s1 s2 = s1 `eltbind` s2

instance TDistr (RSampler g MyElt)
                (RSampler g (MyTraced Int))
                (RSampler g (MyWTraced Int)) where
  pushForward = eltfmap (\x -> MyTraced (x, emptyTrace))
  pushForwardW = eltfmap (\x -> MyWTraced (x, emptyTrace, 1.0))

input3 = Ret $ MyElt Tails
         :: GenFn Int (RSampler StdGen MyElt) MyElt MySet
input3a = Sample (0 :: Int)
                 (makeRSampler $ MyElt Tails
                  :: RSampler StdGen MyElt MySet)
                 (\(MyElt x) -> if x == Tails then 1.0 else 0.0)
drunkenNot3 k (MyElt x) =
  Sample
    k
    (RSampler $ fromList [(MyElt $ myNot x, 0.9), (MyElt x, 0.1)])
    (\(MyElt y) ->
       if y == x then 0.1 else if y == myNot x then 0.9 else 0.0)
computed3 =
  Semicolon (Semicolon input3 (drunkenNot3 1)) (drunkenNot3 2)
computed3a =
  Semicolon (Semicolon input3a (drunkenNot3 1)) (drunkenNot3 2)

test3 n = do
  flips <- sequence . (replicate n) . rsample . runGen $ computed3
  let tails = filter (== MyElt Tails) flips
  -- Output will be ~0.82:
  putStrLn . show $ fromIntegral (length tails) / fromIntegral n

-- try:
-- rsample $ runGen computed3
-- rsample $ runGen computed3a
-- rsample . runGen $ tracing computed3
-- rsample . runGen $ tracing computed3a
-- rsample . runGen $ infer tObs computed3a
-- ...
-- test3 100

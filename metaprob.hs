{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}

import Control.Monad.Random

--
-- METAPROB
--

-- The first section this code, INTERFACE, shows how Metaprob rests
-- atop an abstract theory of distributions (and traces).  It
-- clarifies which aspects of distributions are required to define
-- generative functions, the key transformations among them, and the
-- meta-circular evaluator.
--
-- The second section, EXAMPLES, provides implementations of the
-- interface.  Our implementations of distributions include both
-- measure-theoretic and sampler-theoretic ones.  We set up some
-- sample computations too.
--
-- In all cases, the goal is conceptual clarity, ignoring
-- computational efficiency.

-- This file is intended to be loaded in ghci via
-- > :l metaprob.hs
-- followed by the suggestions under the "try:"s comments in the
-- examples below.

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
--     We assume that A is essentially a finite discrete set,
--     though the code might sometimes work more generally.
--   * We fix some parametric type f(A) in the world of the paper.
--     * Key examples: f(A) = A, and f(A) = A x Trace.
-- The rest of the correspondence is documented as we go.

-- Describes
--   * distributions R(f(A)) = `distr`
-- on
--   * elements f(A) = `elt a`
-- (Note: if `elt a` were just `a`, we would be describing none other
-- than a functor (pushForward) and monad (dirac, convolve) here.)
class Distr distr where
  pushForward :: (elt a -> elt' a) -> distr elt a -> distr elt' a
  dirac :: elt a -> distr elt a
  convolve :: Eq (elt a) =>
              distr elt a -> (elt a -> distr elt a) -> distr elt a

-- Defines generative functions P(f(A)) in terms of f(A) and R(f(A))
data GenFn key distr elt a =
  Sample key (distr elt a) (elt a -> Double) |
  Ret (elt a) |
  Semicolon (GenFn key distr elt a) (elt a -> GenFn key distr elt a)

-- Defines the "Gen" interpretation [[ ]]_g from P(f(A)) to R(f(A))
runGen :: (Distr distr, Eq (elt a)) =>
          GenFn key distr elt a -> distr elt a
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
-- Generative functions of these types are then related by tracing and
-- infer, below.
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

-- Defines tracing from P(A) to P(A x Tracing)
tracing :: (Trace trace key elt traced wtraced, Distr distr) =>
           GenFn key distr elt a ->
           GenFn key distr traced a
tracing (Sample k dist score) =
  Semicolon
    (Sample k
            (pushForward (\x -> makeTraced (x, emptyTrace)) dist)
            (extendByZero score))
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
infer :: (Trace trace key elt traced wtraced, Distr distr,
          Eq key) =>
         trace a -> GenFn key distr elt a ->
         GenFn key distr wtraced a
infer tr (Sample k dist score) =
  Semicolon
    (case traceValue tr k of
       Observe x -> Ret $ makeWTraced (x, emptyTrace, score x)
       Intervene x -> Ret $ makeWTraced (x, emptyTrace, 1.0)
       _ ->
         Semicolon
           (Sample k
                   (pushForward
                      (\x -> makeWTraced (x, emptyTrace, 1.0))
                      dist)
                   (extendByZeroW score))
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

-- Trace-related things

newtype MyElt a = MyElt { myElt :: a } deriving Eq
instance Show a => Show (MyElt a) where
  show (MyElt a) = show a

newtype MyTrace key a =
  MyTrace { myTrace :: [(key, TValue (MyElt a))] }
  deriving Eq
instance (Show key, Show a) => Show (MyTrace key a) where
  show (MyTrace t) = "Trace " ++ show t

newtype MyTraced key a =
  MyTraced { myTraced :: (MyElt a, MyTrace key a) }
  deriving Eq
instance (Show key, Show a) => Show (MyTraced key a) where
  show (MyTraced (MyElt x, MyTrace t)) = show (x, t)

newtype MyWTraced key a =
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

-- Example/omputation-related things

data MySet = Tails | Heads deriving (Show, Eq)
myNot Tails = Heads
myNot Heads = Tails

input :: GenFn key distr MyElt MySet
input = Ret $ MyElt Tails
input' :: Distr distr => GenFn Int distr MyElt MySet
input' = Sample (0 :: Int)
                (dirac $ MyElt Tails)
                (\(MyElt x) -> if x == Tails then 1.0 else 0.0)

drunkenNot :: (MySet -> distr MyElt MySet) -> key ->
              MyElt MySet -> GenFn key distr MyElt MySet
drunkenNot d k (MyElt x) =
  Sample
    k
    (d x)
    (\(MyElt y) -> if y == x       then 0.1
              else if y == myNot x then 0.9
                                   else 0.0)

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

newtype Diracs elt a = Diracs { diracs :: [(elt a, Double)] }
instance Show (elt a) => Show (Diracs elt a) where
  show (Diracs d) = "Diracs" ++ concat (map (\l -> "\n " ++ show l) d)
instance Distr Diracs where
  pushForward f = Diracs . map (\(x, u) -> (f x, u)) . diracs
  dirac x = Diracs [(x, 1.0)]
  convolve d1 d2 = Diracs . squashDiracs . concat $
    map (\xu -> let (x, u) = xu in
                map (\yv -> let (y, v) = yv in (y, u * v))
                    (diracs $ d2 x))
        (diracs d1)

tracing1 = tracing
  :: GenFn Int Diracs MyElt MySet ->
     GenFn Int Diracs (MyTraced Int) MySet
infer1 = infer
  :: MyTrace Int MySet -> GenFn Int Diracs MyElt MySet ->
     GenFn Int Diracs (MyWTraced Int) MySet

input1 = input :: GenFn Int Diracs MyElt MySet
input1' = input' :: GenFn Int Diracs MyElt MySet
drunkenNot1 =
  drunkenNot (\x -> Diracs [(MyElt $ myNot x, 0.9), (MyElt x, 0.1)])
computed1 =
  Semicolon (Semicolon input1 (drunkenNot1 1)) (drunkenNot1 2)
computed1' =
  Semicolon (Semicolon input1' (drunkenNot1 1)) (drunkenNot1 2)

-- try:
-- > runGen computed1
-- > runGen computed1'
-- > runGen $ tracing1 computed1
-- > runGen $ tracing1 computed1'
-- > runGen $ infer1 tObs computed1'
-- ...


--
-- Example 2:
-- Executing determinstic sampling prodedures.  This is a conceptual
-- warm-up for Example 3 below.
--

newtype DSampler elt a = DSampler { dsampler :: () -> elt a }
instance Show (elt a) => Show (DSampler elt a) where
  show s = "() -> " ++ show (dsampler s ())
instance Distr DSampler where
  pushForward f = DSampler . (\x -> f . x) . dsampler
  dirac x = DSampler (\_ -> x)
  convolve s1 s2 = s2 $ dsampler s1 ()

tracing2 = tracing
  :: GenFn Int DSampler MyElt MySet ->
     GenFn Int DSampler (MyTraced Int) MySet
infer2 = infer
  :: MyTrace Int MySet -> GenFn Int DSampler MyElt MySet ->
     GenFn Int DSampler (MyWTraced Int) MySet

input2 = input :: GenFn Int DSampler MyElt MySet
input2' = input' :: GenFn Int DSampler MyElt MySet
-- This is especially not stochastic:
drunkenNot2 = drunkenNot (\x -> dirac $ MyElt $ myNot x)
computed2 =
  Semicolon (Semicolon input2 (drunkenNot2 1)) (drunkenNot2 2)
computed2' =
  Semicolon (Semicolon input2' (drunkenNot2 1)) (drunkenNot2 2)

-- try:
-- > runGen computed2
-- > runGen computed2'
-- > runGen $ tracing2 computed2
-- > runGen $ tracing2 computed2'
-- > runGen $ infer2 tObs computed2'
-- ...


--
-- Example 3:
-- Executing randomized/stochastic sampling procedures.
--

newtype RSampler g elt a = RSampler { rsampler :: Rand g (elt a) }
-- This plays the role of the Show instance:
rsample :: RSampler StdGen elt a -> IO (elt a)
rsample = evalRandIO . rsampler
instance RandomGen g => Distr (RSampler g) where
  pushForward f = RSampler . fmap f . rsampler
  dirac x = RSampler $ uniform [x]
  convolve s1 s2 = RSampler $ (rsampler s1) >>= (\x -> rsampler (s2 x))

tracing3 = tracing
  :: GenFn Int (RSampler StdGen) MyElt MySet ->
     GenFn Int (RSampler StdGen) (MyTraced Int) MySet
infer3 = infer
  :: MyTrace Int MySet -> GenFn Int (RSampler StdGen) MyElt MySet ->
     GenFn Int (RSampler StdGen) (MyWTraced Int) MySet

input3 = input :: GenFn Int (RSampler StdGen) MyElt MySet
input3' = input' :: GenFn Int (RSampler StdGen) MyElt MySet
drunkenNot3 =
  drunkenNot
    (\x -> RSampler $ fromList [(MyElt $ myNot x, 0.9), (MyElt x, 0.1)])
computed3 =
  Semicolon (Semicolon input3 (drunkenNot3 1)) (drunkenNot3 2)
computed3' =
  Semicolon (Semicolon input3' (drunkenNot3 1)) (drunkenNot3 2)

test3 n = do
  flips <- sequence . (replicate n) . rsample . runGen $ computed3
  let tails = filter (== MyElt Tails) flips
  -- Output will be ~0.82:
  putStrLn . show $ fromIntegral (length tails) / fromIntegral n

-- try:
-- > rsample $ runGen computed3
-- > rsample $ runGen computed3'
-- > rsample . runGen $ tracing3 computed3
-- > rsample . runGen $ tracing3 computed3'
-- > rsample . runGen $ infer3 tObs computed3'
-- ...
-- > test3 100

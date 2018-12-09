{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}

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
--   * Stochasticity in "sampling" example using a random monad
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
infer t (Sample k dist score) =
  Semicolon
    (case traceValue t k of
       Observe x -> Ret $ makeWTraced (x, emptyTrace, score x)
       Intervene x -> Ret $ makeWTraced (x, emptyTrace, 1.0)
       _ ->
         Semicolon
           (Sample k (pushForwardW dist) (extendByZeroW score))
           (\xtw -> let (x, _, _) = getWTraced xtw in
                    Ret $ makeWTraced (x, emptyTrace, 1.0)))
    (\ytw -> let (y, _, w) = getWTraced ytw in
             Ret $ makeWTraced (y, kvTrace k (Traced y), w))
infer t (Ret x) = Ret $ makeWTraced (x, emptyTrace, 1.0)
infer t (Semicolon p1 p2) =
  Semicolon
    (infer t p1)
    (\xsv -> let (x, s, v) = getWTraced xsv in
             Semicolon
               (infer t (p2 x))
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
-- Meta-example 1:
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

--
-- Infra-example 1:
-- All the unknown random state consists of a single coin toss outcome.
--

input = Ret $ MyElt Tails :: GenFn Int (Diracs MyElt) MyElt MySet
input2 = Sample (0 :: Int)
                (Diracs [(MyElt Tails, 1.0)])
                (\(MyElt x) -> if x == Tails then 1.0 else 0.0)
drunkenNot k (MyElt x) =
  Sample
    k
    (Diracs [(MyElt $ myNot x, 0.9), (MyElt x, 0.1)])
    (\(MyElt y) ->
       if y == x then 0.1 else if y == myNot x then 0.9 else 0)
computed = Semicolon (Semicolon input (drunkenNot 1)) (drunkenNot 2)
computed2 = Semicolon (Semicolon input2 (drunkenNot 1)) (drunkenNot 2)

-- try:
-- runGen computed
-- runGen computed2
-- runGen $ tracing computed
-- runGen $ tracing computed2
-- runGen $ infer tObs computed2
-- ...

--
-- Meta-example 2: Executing sampling prodedures
--

-- TODO: hook into a random monad; the sample is deterministic for now

data Sampler elt a = Sampler { sampler :: () -> elt a }
makeSampler :: elt a -> Sampler elt a
makeSampler x = Sampler (\_ -> x)
sample :: Sampler elt a -> elt a
sample (Sampler s) = s ()
instance Show (elt a) => Show (Sampler elt a) where
  show s = "() -> " ++ show (sample s)
instance Distr (Sampler elt) elt where
  dirac = makeSampler
  convolve s1 s2 = s2 $ sample s1

instance TDistr (Sampler MyElt)
                (Sampler (MyTraced Int))
                (Sampler (MyWTraced Int)) where
  pushForward s =
    makeSampler $ MyTraced (sample s, emptyTrace)
  pushForwardW s =
    makeSampler $ MyWTraced (sample s, emptyTrace, 1.0)

--
-- Infra-example 2:
--

inptt = Ret $ MyElt Tails :: GenFn Int (Sampler MyElt) MyElt MySet
inptt2 = Sample (0 :: Int)
                (makeSampler $ MyElt Tails)
                (\(MyElt x) -> if x == Tails then 1.0 else 0.0)
-- This is especially not stochastic right now:
drunkenNtt k (MyElt x) =
  Sample
    k
    (makeSampler . MyElt $ myNot x)
    (\(MyElt y) ->
       if y == x then 0.1 else if y == myNot x then 0.9 else 0)
comptted = Semicolon (Semicolon inptt (drunkenNtt 1)) (drunkenNtt 2)
comptted2 = Semicolon (Semicolon inptt2 (drunkenNtt 1)) (drunkenNtt 2)

-- try: (the analogous things)

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

--
-- Interface for Metaprob
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
runGen :: (Eq (elt a), Distr distr elt) =>
          GenFn key distr elt a -> distr a
runGen (Sample k sample score) = sample
runGen (Ret e) = dirac e
runGen (Semicolon p1 p2) = convolve (runGen p1) (runGen . p2)

data TValue a = TNone String | Intervene a | Observe a
                deriving (Eq, Show)
-- Describes the types Trace and A x Trace
class Trace wtraced traced trace elt |
      trace -> wtraced traced elt, traced -> trace, wtraced -> trace where
  getTrace :: trace key a -> [(key, TValue (elt a))]
  emptyTrace :: trace key a
  kvTrace :: key -> TValue (elt a) -> trace key a
  appendTrace :: trace key a -> trace key a -> trace key a
  getTraced :: traced key a -> (elt a, trace key a)
  makeTraced :: elt a -> trace key a -> traced key a
  getWTraced :: wtraced key a -> (elt a, trace key a, Double)
  makeWTraced :: elt a -> trace key a -> Double -> wtraced key a
traceValue :: (Trace wtraced traced trace elt, Eq key) =>
              trace key a -> key -> TValue (elt a)
traceValue t k = let res = filter (\(k', v) -> k' == k) (getTrace t) in
                 if null res then TNone "" else snd $ head res
extendByZero :: Trace wtraced traced trace elt =>
                (elt a -> Double) -> traced key a -> Double
extendByZero f xt = let (x, t) = getTraced xt in
                    if null $ getTrace t then f x else 0.0
extendByZeroW :: Trace wtraced traced trace elt =>
                 (elt a -> Double) -> wtraced key a -> Double
extendByZeroW f xtw = let (x, t, _) = getWTraced xtw in
                     if null $ getTrace t then f x else 0.0

-- Describes how R(A x Trace) should relate to R(A)
class Trace wtraced traced trace elt =>
      TDistr wtdistr wtraced tdistr traced trace distr elt |
      distr -> wtdistr wtraced tdistr traced where
  pushForward :: distr a -> tdistr key a
  pushForwardW :: distr a -> wtdistr key a

-- We get P(A x Tracing) as `GenFn key (tdistr key) (traced key) a`.

-- Defines the transformation tracing from P(A) to P(A x Tracing)
tracing :: (TDistr wtdistr wtraced tdistr traced trace distr elt,
            Show (elt a)) =>
           GenFn key distr elt a ->
           GenFn key (tdistr key) (traced key) a
tracing (Sample k dist score) = Semicolon
  (Sample k (pushForward dist) (extendByZero score))
  (\xt -> let (x, _) = getTraced xt in
          Ret $ makeTraced x (kvTrace k (TNone $ show x)))
tracing (Ret x) = Ret $ makeTraced x emptyTrace
tracing (Semicolon p1 p2) =
  Semicolon
    (tracing p1)
    (\xs -> let (x, s) = getTraced xs in
            Semicolon
              (tracing (p2 x))
              (\yt -> let (y, t) = getTraced yt in
                      Ret $ makeTraced y (appendTrace s t)))

-- Defines the transformation infer_t from P(A) to P(A x Tracing x R^+)
infer :: (TDistr wtdistr wtraced tdistr traced trace distr elt,
          Show (elt a), Eq key) =>
         trace key a -> GenFn key distr elt a ->
         GenFn key (wtdistr key) (wtraced key) a
infer t (Sample k dist score) =
  Semicolon
    (case traceValue t k of
      Observe x -> Ret $ makeWTraced x emptyTrace (score x)
      Intervene x -> Ret $ makeWTraced x emptyTrace 1.0
      TNone _ -> Semicolon
        (Sample k (pushForwardW dist) (extendByZeroW score))
        (\xsv -> let (x, _, _) = getWTraced xsv in
                 Ret $ makeWTraced x emptyTrace 1.0))
    (\ytw -> let (y, _, w) = getWTraced ytw in
             Ret $ makeWTraced y (kvTrace k (TNone $ show y)) w)
infer t (Ret x) = Ret $ makeWTraced x emptyTrace 1.0
infer t (Semicolon p1 p2) =
  Semicolon
    (infer t p1)
    (\xsv -> let (x, s, v) = getWTraced xsv in
             Semicolon
               (infer t (p2 x))
               (\ytw -> let (y, t, w) = getWTraced ytw in
                        Ret $ makeWTraced y (appendTrace s t) (v * w)))

--
-- Examples
--

--
-- Default implementation of shared items
--

data MyElt a = MyElt { myElt :: a } deriving Eq
instance Show a => Show (MyElt a) where
  show (MyElt a) = "MyElt " ++ show a
data MyTrace key a = MyTrace { myTrace :: [(key, TValue (MyElt a))] }
                     deriving Eq
instance (Show key, Show a) => Show (MyTrace key a) where
  show (MyTrace t) = "MyTrace " ++ show t
data MyTraced key a =
  MyTraced { myTraced :: (MyElt a, MyTrace key a) }
  deriving Eq
instance (Show key, Show a) => Show (MyTraced key a) where
  show (MyTraced xt) = "MyTraced " ++ show xt
data MyWTraced key a =
  MyWTraced { myWTraced :: (MyElt a, MyTrace key a, Double) }
  deriving Eq
instance (Show key, Show a) => Show (MyWTraced key a) where
  show (MyWTraced xtw) = "MyWTrace " ++ show xtw
instance Trace MyWTraced MyTraced MyTrace MyElt where
  getTrace = myTrace
  emptyTrace = MyTrace []
  kvTrace k v = MyTrace [(k, v)]
  appendTrace t1 t2 = MyTrace (myTrace t1 ++ myTrace t2)
  getTraced = myTraced
  makeTraced x t = MyTraced (x, t)
  getWTraced = myWTraced
  makeWTraced x t w = MyWTraced (x, t, w)

data MySet = Tails | Heads deriving (Show, Eq)
myNot Tails = Heads
myNot Heads = Tails

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

data Diracs a = Diracs { diracs :: [(MyElt a, Double)] }
instance (Show a) => Show (Diracs a) where
  show (Diracs d) = "Diracs" ++ concat (map (\l -> "\n  " ++ show l) d)
instance Distr Diracs MyElt where
  dirac x = Diracs [(x, 1.0)]
  convolve d1 d2 = Diracs . squashDiracs . concat $
    map (\xu -> let (x, u) = xu in
                map (\yv -> let (y, v) = yv in (y, u * v))
                    (diracs $ d2 x))
        (diracs d1)

data TDiracs key a = TDiracs { tdiracs :: [(MyTraced key a, Double)] }
instance (Show key, Show a) => Show (TDiracs key a) where
  show (TDiracs d) = "TDiracs" ++ concat (map (\l -> "\n  " ++ show l) d)
instance Distr (TDiracs key) (MyTraced key) where
  dirac xt = TDiracs [(xt, 1.0)]
  convolve d1 d2 = TDiracs . squashDiracs . concat $
    map (\xu -> let (x, u) = xu in
                map (\yv -> let (y, v) = yv in (y, u * v))
                    (tdiracs $ d2 x))
        (tdiracs d1)

data WTDiracs key a =
  WTDiracs { wtdiracs :: [(MyWTraced key a, Double)] }
instance (Show key, Show a) => Show (WTDiracs key a) where
  show (WTDiracs d) = "WTDiracs" ++ concat (map (\l -> "\n  " ++ show l) d)
instance Distr (WTDiracs key) (MyWTraced key) where
  dirac xtw = WTDiracs [(xtw, 1.0)]
  convolve d1 d2 = WTDiracs . squashDiracs . concat $
    map (\xu -> let (x, u) = xu in
                map (\yv -> let (y, v) = yv in (y, u * v))
                    (wtdiracs $ d2 x))
        (wtdiracs d1)

instance TDistr WTDiracs MyWTraced TDiracs MyTraced MyTrace Diracs MyElt where
  pushForward =
    TDiracs . map (\(x, u) -> (makeTraced x emptyTrace, u)) . diracs
  pushForwardW =
    WTDiracs . map (\(x, u) -> (makeWTraced x emptyTrace 1.0, u)) . diracs

--
-- Infra-example 1:
-- All the unknown random state consists of a single coin toss outcome.
--

input = Ret $ MyElt Tails :: GenFn Integer Diracs MyElt MySet
input2 = Sample 0
                (Diracs [(MyElt Tails, 1.0)])
                (\(MyElt x) -> if x == Tails then 1.0 else 0.0)
drunkenNot k (MyElt x) = Sample
  k
  (Diracs [(MyElt $ myNot x, 0.9), (MyElt x, 0.1)])
  (\(MyElt y) ->
     if y == x then 0.1 else if y == myNot x then 0.9 else 0)
computed = Semicolon (Semicolon input (drunkenNot 1)) (drunkenNot 2)
computed2 = Semicolon (Semicolon input2 (drunkenNot 1)) (drunkenNot 2)

tObs = MyTrace [(0,Observe (MyElt Heads))]
tInt = MyTrace [(0,Intervene (MyElt Heads))]

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

data Sampler a = Sampler { sampler :: () -> a }
makeSampler :: a -> Sampler a
makeSampler x = Sampler (\_ -> x)
sample :: Sampler a -> a
sample (Sampler s) = s ()
instance Show a => Show (Sampler a) where
  show s = "() -> " ++ show (sample s)
instance Distr Sampler MyElt where
  dirac = makeSampler . myElt
  convolve s1 s2 = s2 $ MyElt (sample s1)

data TSampler key a = TSampler { tsampler :: () -> MyTraced key a  }
makeTSampler :: MyTraced key a -> TSampler key a
makeTSampler x = TSampler (\_ -> x)
tsample :: TSampler key a -> MyTraced key a
tsample d = tsampler d ()
instance (Show a, Show key) => Show (TSampler key a) where
  show ts = "() -> " ++ show (tsample ts)
instance Distr (TSampler key) (MyTraced key) where
  dirac = makeTSampler
  convolve s1 s2 = s2 $ tsample s1

data WTSampler key a = WTSampler { wtsampler :: () -> MyWTraced key a  }
makeWTSampler :: MyWTraced key a -> WTSampler key a
makeWTSampler x = WTSampler (\_ -> x)
wtsample :: WTSampler key a -> MyWTraced key a
wtsample d = wtsampler d ()
instance (Show a, Show key) => Show (WTSampler key a) where
  show ts = "() -> " ++ show (wtsample ts)
instance Distr (WTSampler key) (MyWTraced key) where
  dirac = makeWTSampler
  convolve s1 s2 = s2 $ wtsample s1

instance TDistr
         WTSampler MyWTraced TSampler MyTraced MyTrace Sampler MyElt
         where
  pushForward s =
    makeTSampler $ MyTraced (MyElt $ sample s, emptyTrace)
  pushForwardW s =
    makeWTSampler $ MyWTraced (MyElt $ sample s, emptyTrace, 1.0)

--
-- Infra-example 2:
--

-- (Recall MySet, myNot from Infra-example 1.)

inptt = Ret $ MyElt Tails :: GenFn Integer Sampler MyElt MySet
inptt2 = Sample 0
                (makeSampler Tails)
                (\(MyElt x) -> if x == Tails then 1.0 else 0.0)
-- This is especially not stochastic right now:
drunkenNtt k (MyElt x) = Sample
  k
  (makeSampler $ myNot x)
  (\(MyElt y) ->
     if y == x then 0.1 else if y == myNot x then 0.9 else 0)
comptted = Semicolon (Semicolon inptt (drunkenNtt 1)) (drunkenNtt 2)
comptted2 = Semicolon (Semicolon inptt2 (drunkenNtt 1)) (drunkenNtt 2)

-- try: (the analogous things)

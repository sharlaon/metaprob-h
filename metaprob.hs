{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- Here is our notation compared with the Metaprob paper
-- `key` plays the role of K.
-- `a` plays the role of A.
-- `elt a` represents f(A) for some fixed parametric type in the world
--   of the paper.  Key examples: f(A) = A, or f(A) = A x Trace.
-- `distr a` represents distributions R(f(A)).
-- `GenFn key distr elt a` represents generative functions `P(f(A))`.
-- `runGen p` corresponds to [[p]]_g.

data GenFn key distr elt a =
  Sample key (distr a) |
  Ret (elt a) |
  Semicolon (GenFn key distr elt a) (elt a -> GenFn key distr elt a)

class Distr distr elt | distr -> elt where
  dirac :: elt a -> distr a
  convolve :: Eq a => distr a -> (elt a -> distr a) -> distr a
  runGen :: Eq a => GenFn key distr elt a -> distr a
  runGen (Sample key sample) = sample
  runGen (Ret e) = dirac e
  runGen (Semicolon p1 p2) = convolve (runGen p1) (runGen . p2)

class Tracing1 trace where
  emptyTrace :: trace key
  kvTrace :: key -> String -> trace key
  appendTrace :: trace key -> trace key -> trace key
  getTrace :: trace key -> [(key,String)]

class Tracing1 trace =>
      Tracing2 traced trace elt |
      traced -> trace, traced -> elt where
  makeTraced :: elt a -> trace key -> traced key a
  getTraced :: traced key a -> (elt a, trace key)
  getTracedVal :: traced key a -> elt a
  getTracedTr :: traced key a -> trace key
  withEmptyTrace :: elt a -> traced key a
  withEmptyTrace x = makeTraced x emptyTrace
  extendByZero :: (elt a -> Double) -> (traced key a -> Double)

class Tracing2 traced trace elt =>
      Tracing3 tdistr traced trace distr elt |
      tdistr -> traced distr, traced -> trace elt, distr -> tdistr elt where
  -- Needed for runTracing
  pushForward :: distr a -> tdistr key a
  -- Needed for runGen after runTracing
  tdirac :: traced key a -> tdistr key a
  tconvolve ::
    (Eq a, Eq key) =>
    tdistr key a -> (traced key a -> tdistr key a) -> tdistr key a

instance (Eq key, Tracing3 tdistr traced trace distr elt) =>
         Distr (tdistr key) (traced key) where
  dirac = tdirac
  convolve = tconvolve

-- This corresponds to the transformation tracing from P(A) to P(A x
-- Tracing) in the paper.
tracing :: (Tracing3 tdistr traced trace distr elt, Show (elt a)) =>
           GenFn key distr elt a
             -> GenFn key (tdistr key) (traced key) a
tracing (Sample k dist) = Semicolon
  (Sample k $ pushForward dist)
  (\xt -> let x = getTracedVal xt in
          Ret $ makeTraced x $ kvTrace k $ show x)
tracing (Ret x) = Ret $ withEmptyTrace x
tracing (Semicolon p1 p2) = Semicolon
  (tracing p1)
  (\xs -> Semicolon
    (tracing (p2 $ getTracedVal xs))
    (\yt -> Ret $ makeTraced
      (getTracedVal yt)
      (appendTrace (getTracedTr xs) (getTracedTr yt))))


-- Default implementation of shared items
data MyElt a = MyElt { myElt :: a } deriving (Eq, Show)
data MyTrace key = MyTrace { myTrace :: [(key, String)] }
     deriving (Eq, Show)
instance Tracing1 MyTrace where
  emptyTrace = MyTrace []
  kvTrace k v = MyTrace [(k, v)]
  appendTrace t1 t2 = MyTrace (myTrace t1 ++ myTrace t2)
  getTrace = myTrace
data MyTraced key a = MyTraced
  { myTraced :: (MyElt a, MyTrace key) } deriving (Eq, Show)
instance Tracing2 MyTraced MyTrace MyElt where
  makeTraced x t = MyTraced (x, t)
  getTraced = myTraced
  getTracedVal = fst . myTraced
  getTracedTr = snd . myTraced
  extendByZero f xt = let (x, t) = myTraced xt in
                      if null $ myTrace t then f x else 0.0

-- Meta-example: Measure-theoretically, tracking point masses in the
-- support of the distribution
squashDiracs :: Eq a => [(a, Double)] -> [(a, Double)]
squashDiracs [] = []
squashDiracs ((x,v):xvs) =
  let yws = squashDiracs xvs
      hit = filter (\yw -> fst yw == x) yws
      miss = filter (\yw -> fst yw /= x) yws in
  if null hit then (x,v):yws else (x, v + (snd . head $ hit)):miss
data Diracs a = Diracs { diracs :: [(MyElt a, Double)] }
     deriving Show
instance Distr Diracs MyElt where
  dirac x = Diracs [(x, 1.0)]
  convolve d1 d2 = Diracs . squashDiracs . concat $
    map (\xu -> let (x, u) = xu in
                map (\yv -> let (y, v) = yv in (y, u * v))
                    (diracs $ d2 x))
        (diracs d1)
data TDiracs key a = TDiracs { tdiracs :: [(MyTraced key a, Double)] }
     deriving Show
instance Tracing3 TDiracs MyTraced MyTrace Diracs MyElt where
  pushForward =
    TDiracs . map (\(x, u) -> (makeTraced x emptyTrace, u)) . diracs
  tdirac xt = TDiracs [(xt, 1.0)]
  tconvolve d1 d2 = TDiracs . squashDiracs . concat $
    map (\xu -> let (x, u) = xu in
                map (\yv -> let (y, v) = yv in (y, u * v))
                    (tdiracs $ d2 x))
        (tdiracs d1)
  
-- Infra-example:
-- All the unknown random state consists of a single coin toss outcome.
data MySet = Tails | Heads deriving (Show, Eq)

input = Ret $ MyElt Tails :: GenFn Integer Diracs MyElt MySet
input2 = Sample 0 $ Diracs [(MyElt Tails, 1.0)]
  :: GenFn Integer Diracs MyElt MySet
drunkenNot key (MyElt x) = Sample key . Diracs $
  if x == Heads then [(MyElt Tails, 0.9), (MyElt Heads, 0.1)]
                else [(MyElt Tails, 0.1), (MyElt Heads, 0.9)]
computed = Semicolon (Semicolon input (drunkenNot 1)) (drunkenNot 2)
computed2 = Semicolon (Semicolon input2 (drunkenNot 1)) (drunkenNot 2)

-- try:
-- runGen computed
-- runGen . tracing $ computed
-- vs.:
-- runGen computed2
-- runGen . tracing $ computed2

-- Meta-example: Executing sampling prodedures
data Sampler a = Sampler { sampler :: () -> a }
makeSampler :: a -> Sampler a
makeSampler x = Sampler (\_ -> x)
sample :: Sampler a -> a
sample (Sampler s) = s ()
instance Show a => Show (Sampler a) where
  show (Sampler s) = "() -> " ++ show (s ())
instance Distr Sampler MyElt where
  dirac = makeSampler . myElt
  convolve (Sampler s1) s2 = s2 . MyElt . s1 $ ()
data TSampler key a = TSampler { tsampler :: () -> MyTraced key a  }
makeTSampler :: MyTraced key a -> TSampler key a
makeTSampler x = TSampler (\_ -> x)
tsample :: TSampler key a -> MyTraced key a
tsample d = tsampler d ()
instance (Show a, Show key) => Show (TSampler key a) where
  show (TSampler ts) = "() -> " ++ (show $ ts ())
instance Tracing3 TSampler MyTraced MyTrace Sampler MyElt where
  pushForward (Sampler s) =
    makeTSampler $ MyTraced (MyElt $ s (), emptyTrace)
  tdirac = makeTSampler
  tconvolve (TSampler s1) s2 = s2 . s1 $ ()

-- Infra-example:

inptt = Ret $ MyElt Tails :: GenFn Integer Sampler MyElt MySet
inptt2 = Sample 0 $ Sampler (\_ -> Tails)
  :: GenFn Integer Sampler MyElt MySet
-- Currently there is no way to do drunkenNot non-deterministically
ntt Tails = Heads
ntt Heads = Tails
drunkenNtt key (MyElt x) = Sample key . makeSampler . ntt $ x
comptted = Semicolon (Semicolon inptt (drunkenNtt 1)) (drunkenNtt 2)
comptted2 = Semicolon (Semicolon inptt2 (drunkenNtt 1)) (drunkenNtt 2)

-- try:
-- runGen comptted
-- runGen . tracing $ comptted
-- vs.:
-- runGen comptted2
-- runGen . tracing $ comptted2

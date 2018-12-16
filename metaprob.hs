{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuantifiedConstraints #-}

import Data.Dynamic
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
--   * Some notion of continuous distributions


--
-- INTERFACE
--

-- We describe the relationship between our notation and that of the
-- paper as we go.  We assume that the type A there is a finite
-- discrete set, although the code may accidentally work more
-- generally.

-- Describes operations we use on types throughout.
-- The variable `a` here is either A from the paper, or f(A) below.
class (Eq a, Show a, Typeable a) => BaseType a where

-- Describes the operations on A carrying over to a parametric type
-- f(A) in the world of the paper.
class (forall a. BaseType a => BaseType (elt a), Typeable elt) =>
      EltType elt where

-- Describes distributions R(f(A)) on f(A).
class Distr distr where
  pushForward :: (EltType elt, EltType elt', BaseType a) =>
                 (elt a -> elt' a) -> distr elt a -> distr elt' a
  dirac :: (EltType elt, BaseType a) =>
           elt a -> distr elt a
  -- The literature also calls this a "compound" distribution:
  mixture :: (EltType elt, BaseType a, BaseType b) =>
             distr elt a -> (elt a -> distr elt b) -> distr elt b

-- A distribution is morally just a monad applied to the element type.
newtype MDistr m elt a = MDistr { mDistr :: m (elt a) }
instance Monad m => Distr (MDistr m) where
  pushForward f = MDistr . fmap f . mDistr
  dirac = MDistr . return
  mixture s1 s2 = MDistr $ (mDistr s1) >>= (mDistr . s2)

-- Defines generative values in terms of f(A) and R(f(A)).
data GenVal key distr elt a where
  Sample :: (EltType elt, BaseType a) =>
    key -> (distr elt a) -> (elt a -> Double)
    -> GenVal key distr elt a
  Ret :: (EltType elt, BaseType a) =>
    (elt a)
    -> GenVal key distr elt a
  Evaluate :: (EltType elt, BaseType c, BaseType a) =>
    (GenVal key distr elt c) -> (GenFn key distr elt c a)
    -> GenVal key distr elt a

-- Defines generative functions, similarly.
data GenFn key distr elt a b where
  Gen :: (EltType elt, BaseType a, BaseType b) =>
    (elt a -> GenVal key distr elt b)
    -> GenFn key distr elt a b
  Compose :: (EltType elt, BaseType a, BaseType c, BaseType b) =>
    (GenFn key distr elt a c) -> (GenFn key distr elt c b)
    -> GenFn key distr elt a b

-- "Generative procedures" P(f(A)) as in the paper morally consist of
-- `GenVal key distr elt a` and `GenFn key distr elt a a` blended
-- together into one type.

-- Defines the "Gen" interpretation [[ ]]_g from P(f(A)) to R(f(A)).
runGen :: (Distr distr, EltType elt, BaseType a) =>
          GenVal key distr elt a -> distr elt a
runGen (Sample k sample score) = sample
runGen (Ret x) = dirac x
runGen (Evaluate x f) = mixture (runGen x) (runGen' f)

runGen' :: (Distr distr, EltType elt, BaseType a, BaseType b) =>
           GenFn key distr elt a b -> elt a -> distr elt b
runGen' (Gen f) = runGen . f
runGen' (Compose f1 f2) = \x -> mixture (runGen' f1 $ x) (runGen' f2)


data TValue =
  TNone | Traced String | Observe Dynamic | Intervene Dynamic
  deriving Show
instance Eq TValue where
  TNone == TNone = True
  -- The following should be improved.
  -- The paper only ever uses one type A, but we allow heterogeneous
  -- types, forcing us to employ the Dynamic trick above, and losing a
  -- good notion of equality of values.
  -- The only place this `Eq` intance is used is in squashDiracs, so
  -- in that implementation we simply have a failure to properly
  -- simplify mixture distributions when the values are traced.
  _ == _ = False

-- In the context of `class Trace`,
--   * `trace` corrsponds to Trace,
--   * `elt a` corresponds to f(A) = A,
--   * `traced a` corresponds to f(A) = A x Trace, and
--   * `wtraced a` corresponds to f(A) = A x Trace x R^+.
class (Eq trace, BaseType key,
       EltType elt, EltType traced, EltType wtraced) =>
      Trace trace key elt traced wtraced |
      trace -> key elt traced wtraced,
      traced -> trace, wtraced -> traced where
  getTrace :: trace -> [(key, TValue)]
  emptyTrace :: trace
  kvTrace :: key -> TValue -> trace
  appendTrace :: trace -> trace -> trace
  getTraced :: traced a -> (elt a, trace)
  makeTraced :: (elt a, trace) -> traced a
  getWTraced :: wtraced a -> (elt a, trace, Double)
  makeWTraced :: (elt a, trace, Double) -> wtraced a
unTrace :: Trace trace key elt traced wtraced =>
           traced a -> elt a
unTrace xt = let (x, _) = getTraced xt in x
unWTrace :: Trace trace key elt traced wtraced =>
            wtraced a -> elt a
unWTrace xtw = let (x, _, _) = getWTraced xtw in x
emptyTraced :: Trace trace key elt traced wtraced =>
               elt a -> traced a
emptyTraced x = makeTraced (x, emptyTrace)
emptyWTraced :: Trace trace key elt traced wtraced =>
                elt a -> wtraced a
emptyWTraced x = makeWTraced (x, emptyTrace, 1.0)
extendByZero :: Trace trace key elt traced wtraced =>
                (elt a -> Double) -> traced a -> Double
extendByZero f xt = let (x, t) = getTraced xt in
                    if null $ getTrace t then f x else 0.0
extendByZeroW :: Trace trace key elt traced wtraced =>
                 (elt a -> Double) -> wtraced a -> Double
extendByZeroW f xtw = let (x, t, _) = getWTraced xtw in
                      if null $ getTrace t then f x else 0.0
traceValue :: Trace trace key elt traced wtraced =>
              trace -> key -> TValue
traceValue t k = let res = filter ((== k) . fst) (getTrace t) in
                 if null res then TNone else snd $ head res

-- These two functions correspond to the paper's transformation
-- tracing from P(A) to P(A x Tracing).
tracing :: (Trace trace key elt traced wtraced, Distr distr,
            BaseType a) =>
           GenVal key distr elt a ->
           GenVal key distr traced a
tracing (Sample k dist deriv) =
  Evaluate
    (Sample k (pushForward emptyTraced dist) (extendByZero deriv))
    (Gen $ \xt -> let (x, _) = getTraced xt in
                  Ret $ makeTraced
                          (x, kvTrace k (Traced $ show x)))
tracing (Ret x) = Ret $ emptyTraced x
tracing (Evaluate x f) =
  Evaluate
    (tracing x)
    (Gen $ \xs -> let (_, s) = getTraced xs in
                  Evaluate
                    (Evaluate (Ret xs) (tracing' f))
                    (Gen $ \yt -> let (y, t) = getTraced yt in
                                  Ret $ makeTraced
                                          (y, appendTrace s t)))

tracing' :: (Trace trace key elt traced wtraced, Distr distr,
             BaseType a, BaseType b) =>
            GenFn key distr elt a b ->
            GenFn key distr traced a b
tracing' (Gen f) = Gen $ tracing . f . unTrace
tracing' (Compose f1 f2) =
  Compose
    (tracing' f1)
    (Gen $ \xs -> let (_, s) = getTraced xs in
                  Evaluate
                    (Evaluate (Ret xs) (tracing' f2))
                    (Gen $ \yt -> let (y, t) = getTraced yt in
                                  Ret $ makeTraced
                                          (y, appendTrace s t)))

-- These two functions correspond to the paper's transformation
-- infer_t from P(A) to P(A x Tracing x R^+)
infer :: (Trace trace key elt traced wtraced, Distr distr,
          BaseType a) =>
         trace -> GenVal key distr elt a ->
         GenVal key distr wtraced a
infer tr (Sample k dist deriv) =
  Evaluate
    (case traceValue tr k of
       Observe x -> Ret $ let x' = maybe undefined id $ fromDynamic x in
                          makeWTraced (x', emptyTrace, deriv x')
       Intervene x -> Ret $ let x' = maybe undefined id $ fromDynamic x in
                            emptyWTraced x'
       _ ->
         Evaluate
           (Sample k
                   (pushForward emptyWTraced dist)
                   (extendByZeroW deriv))
           (Gen $ \xtw -> let (x, _, _) = getWTraced xtw in
                          Ret $ emptyWTraced x))
    (Gen $ \ys -> let (y, _, s) = getWTraced ys in
                  Ret $ makeWTraced
                          (y, kvTrace k (Traced $ show y), s))
infer tr (Ret x) = Ret $ emptyWTraced x
infer tr (Evaluate x f) =
  Evaluate
    (infer tr x)
    (Gen $ \xsv -> let (_, s, v) = getWTraced xsv in
                   Evaluate
                     (Evaluate (Ret xsv) (infer' tr f))
                     (Gen $ \ytw -> let (y, t, w) = getWTraced ytw in
                                    Ret $ makeWTraced
                                           (y, appendTrace s t, v * w)))

infer' :: (Trace trace key elt traced wtraced, Distr distr,
           BaseType a, BaseType b) =>
          trace -> GenFn key distr elt a b ->
          GenFn key distr wtraced a b
infer' tr (Gen f) = Gen $ infer tr . f . unWTrace
infer' tr (Compose f1 f2) =
  Compose
    (infer' tr f1)
    (Gen $ \xsv -> let (_, s, v) = getWTraced xsv in
                   Evaluate
                     (Evaluate (Ret xsv) (infer' tr f2))
                     (Gen $ \ytw -> let (y, t, w) = getWTraced ytw in
                                    Ret $ makeWTraced
                                           (y, appendTrace s t, v * w)))


--
-- EXAMPLES
--

--
-- Default implementation of shared items
--

-- Trace-related things

newtype MyElt a = MyElt a
  deriving (Eq, Typeable)
instance Show a => Show (MyElt a) where
  show (MyElt a) = show a
instance BaseType a => BaseType (MyElt a) where
instance EltType MyElt where

newtype MyTrace key = MyTrace { myTrace :: [(key, TValue)] }
  deriving (Eq, Typeable)
instance Show key => Show (MyTrace key) where
  show (MyTrace t) = "Trace " ++ show t

newtype MyTraced key a =
  MyTraced { myTraced :: (MyElt a, MyTrace key) }
  deriving (Eq, Typeable)
instance (Show key, Show a) => Show (MyTraced key a) where
  show (MyTraced (MyElt x, MyTrace t)) = show (x, t)
instance (BaseType key, BaseType a) =>
         BaseType (MyTraced key a) where
instance BaseType key => EltType (MyTraced key) where

newtype MyWTraced key a =
  MyWTraced { myWTraced :: (MyElt a, MyTrace key, Double) }
  deriving (Eq, Typeable)
instance (Show key, Show a) => Show (MyWTraced key a) where
  show (MyWTraced (MyElt x, MyTrace t, w)) = show (x, t, w)
instance (BaseType key, BaseType a) =>
         BaseType (MyWTraced key a) where
instance BaseType key => EltType (MyWTraced key) where

instance BaseType key =>
         Trace (MyTrace key)
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

-- Example/computation-related things

instance BaseType Int where

data MySet = Tails | Heads deriving (Eq, Show, Typeable)
instance BaseType MySet where
myNot Tails = Heads
myNot Heads = Tails

input :: GenVal key distr MyElt MySet
input = Ret $ MyElt Tails
input' :: Distr distr => GenVal Int distr MyElt MySet
input' = Sample (0 :: Int)
                (dirac $ MyElt Tails)
                (\(MyElt x) -> if x == Tails then 1.0 else 0.0)

drunkenNotList :: (Fractional t) => MySet -> [(MyElt MySet, t)]
drunkenNotList x = [(MyElt $ myNot x, 0.9), (MyElt x, 0.1)]
drunkenNotScore :: MySet -> MyElt MySet -> Double
drunkenNotScore x (MyElt y) =
  if y == x then 0.1
  else if y == myNot x then 0.9
  else 0.0 -- Not reachable but syntactically required
drunkenNot :: (MySet -> distr MyElt MySet) -> key ->
              GenFn key distr MyElt MySet MySet
drunkenNot d k = Gen $ \(MyElt x) -> Sample k (d x) (drunkenNotScore x)

tObs = MyTrace [(0 :: Int, Observe $ toDyn (MyElt Heads))]
tInt = MyTrace [(0 :: Int, Intervene $ toDyn (MyElt Heads))]


--
-- Example 1:
-- Measure-theoretically, tracking point masses in the support of the
-- distribution.
--

squashDiracs :: Eq a => [(a, Double)] -> [(a, Double)]
squashDiracs [] = []
squashDiracs ((x, v) : xvs) =
  let yws = squashDiracs xvs
      hit = filter (\yw -> fst yw == x) yws
      miss = filter (\yw -> fst yw /= x) yws in
  if null hit then (x, v) : yws
              else (x, v + (snd $ head hit)) : miss

-- The latent monad in this example is similar to the common
-- list/"nondeterminism" monad, but here the list values are distinct,
-- and each value is paired with a weight in R^+.  Whereas the list
-- monad's bind fans out over all possibilities and concatenates, this
-- monad's bind fans out, multiplying weights as it goes, and when it
-- concatenates it collects duplicate values while adding their
-- weights (the effect of `squashDiracs`).
-- The reason we do not define a monad instance is that
-- `squashDiracs`, and therefore the bind operation, requires the
-- condition `Eq (elt a)`, which monads do not let us impose.
newtype Diracs elt a = Diracs { diracs :: [(elt a, Double)] }
instance Show (elt a) => Show (Diracs elt a) where
  show (Diracs d) = "Diracs" ++ concat (map (\l -> "\n " ++ show l) d)
instance Distr Diracs where
  pushForward f = Diracs . map (\(x, u) -> (f x, u)) . diracs
  dirac x = Diracs [(x, 1.0)]
  mixture d1 d2 = Diracs . squashDiracs . concat $
    map (\xu -> let (x, u) = xu in
                map (\yv -> let (y, v) = yv in (y, u * v))
                    (diracs $ d2 x))
        (diracs d1)

tracing1 = tracing
  :: GenVal Int Diracs MyElt MySet ->
     GenVal Int Diracs (MyTraced Int) MySet
infer1 = infer
  :: MyTrace Int -> GenVal Int Diracs MyElt MySet ->
     GenVal Int Diracs (MyWTraced Int) MySet

input1 = input :: GenVal Int Diracs MyElt MySet
input1' = input' :: GenVal Int Diracs MyElt MySet
drunkenNot1 = drunkenNot (\x -> Diracs $ drunkenNotList x)
computed1 =
  Evaluate (Evaluate input1 (drunkenNot1 1)) (drunkenNot1 2)
computed1' =
  Evaluate (Evaluate input1' (drunkenNot1 1)) (drunkenNot1 2)
computed1'' =
  Evaluate input1 $ Compose (drunkenNot1 1) (drunkenNot1 2)
computed1''' =
  Evaluate input1' $ Compose (drunkenNot1 1) (drunkenNot1 2)

-- try:
-- > runGen computed1
-- > runGen computed1'
-- > runGen computed1''
-- > runGen computed1'''
-- > runGen $ tracing1 computed1
-- > runGen $ tracing1 computed1'
-- > runGen $ infer1 tObs computed1'
-- ...


--
-- Example 2:
-- Executing determinstic sampling prodedures.  This is a conceptual
-- warm-up for Example 3 below.
--

-- Sampling procedures are functions with one value, `() -> elt a`,
-- otherwise written `(->) () (elt a)`.
type DSampler = MDistr ((->) ())
instance Show (elt a) => Show (DSampler elt a) where
  show s = "() -> " ++ show (mDistr s ())

tracing2 = tracing
  :: GenVal Int DSampler MyElt MySet ->
     GenVal Int DSampler (MyTraced Int) MySet
infer2 = infer
  :: MyTrace Int -> GenVal Int DSampler MyElt MySet ->
     GenVal Int DSampler (MyWTraced Int) MySet

input2 = input :: GenVal Int DSampler MyElt MySet
input2' = input' :: GenVal Int DSampler MyElt MySet
-- This is especially not stochastic:
drunkenNot2 = drunkenNot (\x -> MDistr (\_ -> MyElt $ myNot x))
computed2 =
  Evaluate (Evaluate input2 (drunkenNot2 1)) (drunkenNot2 2)
computed2' =
  Evaluate (Evaluate input2' (drunkenNot2 1)) (drunkenNot2 2)
computed2'' =
  Evaluate input2 $ Compose (drunkenNot2 1) (drunkenNot2 2)
computed2''' =
  Evaluate input2' $ Compose (drunkenNot2 1) (drunkenNot2 2)

-- try:
-- > runGen computed2
-- > runGen computed2'
-- > runGen computed2''
-- > runGen computed2'''
-- > runGen $ tracing2 computed2
-- > runGen $ tracing2 computed2'
-- > runGen $ infer2 tObs computed2'
-- ...


--
-- Example 3:
-- Executing randomized/stochastic sampling procedures.
--

-- The Rand monad carries along the state of a pseudorandom number
-- generator seed for us.
type RSampler g = MDistr (Rand g)
-- This plays the role of the Show instance.
rsample :: RSampler StdGen elt a -> IO (elt a)
rsample = evalRandIO . mDistr

tracing3 = tracing
  :: GenVal Int (RSampler StdGen) MyElt MySet ->
     GenVal Int (RSampler StdGen) (MyTraced Int) MySet
infer3 = infer
  :: MyTrace Int -> GenVal Int (RSampler StdGen) MyElt MySet ->
     GenVal Int (RSampler StdGen) (MyWTraced Int) MySet

input3 = input :: GenVal Int (RSampler StdGen) MyElt MySet
input3' = input' :: GenVal Int (RSampler StdGen) MyElt MySet
drunkenNot3 =
  drunkenNot (\x -> MDistr . fromList $ drunkenNotList x)
computed3 =
  Evaluate (Evaluate input3 (drunkenNot3 1)) (drunkenNot3 2)
computed3' =
  Evaluate (Evaluate input3' (drunkenNot3 1)) (drunkenNot3 2)
computed3'' =
  Evaluate input3 $ Compose (drunkenNot3 1) (drunkenNot3 2)
computed3''' =
  Evaluate input3' $ Compose (drunkenNot3 1) (drunkenNot3 2)

test3 n = do
  flips <- sequence . (replicate n) . rsample . runGen $ computed3
  let tails = filter (== MyElt Tails) flips
  -- Output will be ~0.82:
  putStrLn . show $ fromIntegral (length tails) / fromIntegral n

-- try:
-- > rsample $ runGen computed3
-- > rsample $ runGen computed3'
-- > rsample $ runGen computed3''
-- > rsample $ runGen computed3'''
-- > rsample . runGen $ tracing3 computed3
-- > rsample . runGen $ tracing3 computed3'
-- > rsample . runGen $ infer3 tObs computed3'
-- ...
-- > test3 100

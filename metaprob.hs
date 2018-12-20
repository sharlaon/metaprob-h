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

-- Describes the space of trace keys.
class BaseType key => Key key where
  nullKey   :: key
  isNullKey :: key -> Bool

-- Describes the operations on A carrying over to a parametric type
-- f(A) in the world of the paper.
class (forall a. BaseType a => BaseType (elt a), Typeable elt) =>
      EltType elt where

-- Describes distributions R(f(A)) on f(A).
-- We assume the following laws hold:
--   * Unit:
--     mixture (dirac x) d = d a
--     mixture d dirac = d
--   * Associativity:
--     mixture (mixture d1 d2) d3
--       = mixture d1 (\x -> mixture (d2 x) d3)
class Distr distr where
  pushForward :: (EltType elt, EltType elt', BaseType a) =>
                 (elt a -> elt' a) -> distr elt a -> distr elt' a
  dirac       :: (EltType elt, BaseType a) =>
                 elt a -> distr elt a
  -- The literature also calls this a "compound" distribution:
  mixture     :: (EltType elt, BaseType a, BaseType b) =>
                 distr elt a -> (elt a -> distr elt b) -> distr elt b

-- A distribution is morally just a monad applied to the element type.
-- The monad laws are the distribution laws.
newtype MDistr m elt a = MDistr { mDistr :: m (elt a) }
instance Monad m => Distr (MDistr m) where
  pushForward f = MDistr . fmap f . mDistr
  dirac         = MDistr . return
  mixture s1 s2 = MDistr $ (mDistr s1) >>= (mDistr . s2)

-- Defines generative values in terms of f(A) and R(f(A)).
data GenVal key distr elt a where
  Sample   :: (Key key, EltType elt, BaseType a) =>
              key -> distr elt a -> (elt a -> Double)
              -> GenVal key distr elt a
  Evaluate :: (EltType elt, BaseType c, BaseType a) =>
              GenVal key distr elt c -> GenFn key distr elt c a
              -> GenVal key distr elt a

kronecker :: (Eq a) => a -> a -> Double
kronecker x y = if x == y then 1.0 else 0.0
ret :: (Key key, Distr distr, EltType elt, BaseType a) =>
       elt a -> GenVal key distr elt a
ret x = Sample nullKey (dirac x) (kronecker x)

-- Defines generative functions, similarly.
data GenFn key distr elt a b where
  Gen     :: (EltType elt, BaseType a, BaseType b) =>
             (elt a -> GenVal key distr elt b)
             -> GenFn key distr elt a b
  Compose :: (EltType elt, BaseType a, BaseType c, BaseType b) =>
             GenFn key distr elt a c -> GenFn key distr elt c b
             -> GenFn key distr elt a b

-- In the paper, "Generative procedures" P(f(A)) morally consist of
-- `GenVal key distr elt a` and `GenFn key distr elt a a` blended
-- together into a single type.

-- Defines the "Gen" interpretation [[ ]]_g from P(f(A)) to R(f(A)).
runGen :: (Key key, Distr distr, EltType elt, BaseType a) =>
          GenVal key distr elt a -> distr elt a
runGen (Sample k sample score) = sample
runGen (Evaluate x f) = mixture (runGen x) (runGen' f)

runGen' :: (Key key, Distr distr,
            EltType elt, BaseType a, BaseType b) =>
           GenFn key distr elt a b -> elt a -> distr elt b
runGen' (Gen f) = runGen . f
runGen' (Compose f1 f2) = \x -> mixture (runGen' f1 x) (runGen' f2)

-- The data structure built from `GenVal` and `GenFn` is *syntactic*,
-- while `runGen` is a *semantic* intepretation.  Under the
-- distribution laws, the semantics obeys:
--   * Unit:
--     runGen $ Evaluate (Sample k (dirac x) s) f
--       = runGen' f x
--     runGen $ Evaluate x (Gen $ \y -> Sample (k y) (dirac y) (s y))
--       = runGen x
--   * Associativity:
--     runGen' $ Compose (Compose f1 f2) f3
--       = runGen' $ Compose f1 (Compose f2 f3)
--     runGen $ Evaluate (Evaluate x f1) f2
--       = runGen $ Evaluate x (Compose f1 f2)
--   * Reconstruction (a tautology):
--     runGen $ Sample k (runGen x) s = runGen x
--     runGen' $ Gen $ \y -> Sample (k y) (runGen' f y) (s y)
--       = runGen' f

-- Describes the entries recorded by a trace structure.
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
  _ == _         = False

-- Describes the type Trace of traces.
class (Key key, Eq trace) => Trace key trace | trace -> key where
  getTrace    :: trace -> [(key, TValue)]
  emptyTrace  :: trace
  kvTrace     :: key -> TValue -> trace
  appendTrace :: trace -> trace -> trace
traceValue :: Trace key trace => trace -> key -> TValue
traceValue t k = let res = filter ((== k) . fst) (getTrace t)
                 in if null res then TNone else snd $ head res

-- In this context, `elt a` corresponds to f(A) = A, and `traced a`
-- corresponds to f(A) = A x Trace.
class (Trace key trace, EltType elt, EltType traced) =>
      Traced key trace elt traced | traced -> trace elt where
  getTraced  :: traced a -> (elt a, trace)
  makeTraced :: (elt a, trace) -> traced a
extendByZero :: Traced key trace elt traced =>
                (elt a -> Double) -> traced a -> Double
extendByZero f xt = let (x, t) = getTraced xt
                    in if null $ getTrace t then f x else 0.0

-- Similarly, here `wtraced a` corresponds to A x Trace x R^+.
class (Trace key trace, EltType elt, EltType wtraced) =>
      WTraced key trace elt wtraced | wtraced -> trace elt where
  getWTraced  :: wtraced a -> (elt a, trace, Double)
  makeWTraced :: (elt a, trace, Double) -> wtraced a
extendByZeroW :: WTraced key trace elt wtraced =>
                 (elt a -> Double) -> wtraced a -> Double
extendByZeroW f xtw = let (x, t, _) = getWTraced xtw
                      in if null $ getTrace t then f x else 0.0

-- These two functions correspond to the paper's transformation
-- tracing from P(A) to P(A x Tracing).
tracing :: (Traced key trace elt traced, Distr distr,
            BaseType a) =>
           GenVal key distr elt a -> GenVal key distr traced a
tracing (Sample k dist deriv) =
  Evaluate
    (Sample k
            (pushForward (\x -> makeTraced (x, emptyTrace)) dist)
            (extendByZero deriv))
    (Gen $ \xt ->
       let (x, _) = getTraced xt
           t      = if isNullKey k then emptyTrace
                                   else kvTrace k (Traced $ show x)
       in ret $ makeTraced (x, t))
tracing (Evaluate x f) =
  Evaluate
    (tracing x)
    (Gen $ \xs ->
       let (_, s) = getTraced xs
       in Evaluate
            (Evaluate (ret xs) (tracing' f))
            (Gen $ \yt -> let (y, t) = getTraced yt
                          in ret $ makeTraced (y, appendTrace s t)))

tracing' :: (Traced key trace elt traced, Distr distr,
             BaseType a, BaseType b) =>
            GenFn key distr elt a b -> GenFn key distr traced a b
tracing' (Gen f) = Gen $ tracing . f . fst . getTraced
tracing' (Compose f1 f2) =
  Compose
    (tracing' f1)
    (Gen $ \xs ->
       let (_, s) = getTraced xs
       in Evaluate
            (Evaluate (ret xs) (tracing' f2))
            (Gen $ \yt -> let (y, t) = getTraced yt
                          in ret $ makeTraced (y, appendTrace s t)))

-- These two functions correspond to the paper's transformation
-- infer_t from P(A) to P(A x Tracing x R^+)
infer :: (WTraced key trace elt wtraced, Distr distr,
          BaseType a) =>
         trace -> GenVal key distr elt a -> GenVal key distr wtraced a
infer tr (Sample k dist deriv) =
  Evaluate
    (case traceValue tr k of
       Observe x   -> ret $ let Just x' = fromDynamic x
                            in makeWTraced (x', emptyTrace, deriv x')
       Intervene x -> ret $ let Just x' = fromDynamic x
                            in makeWTraced (x', emptyTrace, 1.0)
       _ ->
         Evaluate
           (Sample k
                   (pushForward
                     (\x -> makeWTraced (x, emptyTrace, 1.0))
                     dist)
                   (extendByZeroW deriv))
           (Gen $ \xtw -> let (x, _, _) = getWTraced xtw
                          in ret $ makeWTraced (x, emptyTrace, 1.0)))
    (Gen $ \ytw ->
       let (y, _, w) = getWTraced ytw
           (t, w')   = if isNullKey k
                         then (emptyTrace, 1.0)
                         else (kvTrace k (Traced $ show y), w)
       in ret $ makeWTraced (y, t, w'))
infer tr (Evaluate x f) =
  Evaluate
    (infer tr x)
    (Gen $ \xsv ->
       let (_, s, v) = getWTraced xsv
       in Evaluate
            (Evaluate (ret xsv) (infer' tr f))
            (Gen $ \ytw ->
               let (y, t, w) = getWTraced ytw
               in ret $ makeWTraced (y, appendTrace s t, v * w)))

infer' :: (WTraced key trace elt wtraced, Distr distr,
           BaseType a, BaseType b) =>
          trace -> GenFn key distr elt a b ->
          GenFn key distr wtraced a b
infer' tr (Gen f) = Gen $
  infer tr . f . (\(x, _, _) -> x) . getWTraced
infer' tr (Compose f1 f2) =
  Compose
    (infer' tr f1)
    (Gen $ \xsv ->
       let (_, s, v) = getWTraced xsv
       in Evaluate
            (Evaluate (ret xsv) (infer' tr f2))
            (Gen $ \ytw ->
               let (y, t, w) = getWTraced ytw
               in ret $ makeWTraced (y, appendTrace s t, v * w)))


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
instance Key key => Trace key (MyTrace key) where
  getTrace    = myTrace
  emptyTrace  = MyTrace []
  kvTrace k v = MyTrace [(k, v)]
  appendTrace (MyTrace t1) (MyTrace t2) = MyTrace (t1 ++ t2)

newtype MyTraced key a =
  MyTraced { myTraced :: (MyElt a, MyTrace key) }
  deriving (Eq, Typeable)
instance (Show key, Show a) => Show (MyTraced key a) where
  show (MyTraced (MyElt x, MyTrace t)) = show (x, t)
instance (BaseType key, BaseType a) =>
         BaseType (MyTraced key a) where
instance Key key => EltType (MyTraced key) where
instance Key key =>
         Traced key (MyTrace key) MyElt (MyTraced key) where
  getTraced   = myTraced
  makeTraced  = MyTraced

newtype MyWTraced key a =
  MyWTraced { myWTraced :: (MyElt a, MyTrace key, Double) }
  deriving (Eq, Typeable)
instance (Show key, Show a) => Show (MyWTraced key a) where
  show (MyWTraced (MyElt x, MyTrace t, w)) = show (x, t, w)
instance (BaseType key, BaseType a) =>
         BaseType (MyWTraced key a) where
instance Key key => EltType (MyWTraced key) where
instance Key key =>
         WTraced key (MyTrace key) MyElt (MyWTraced key) where
  getWTraced  = myWTraced
  makeWTraced = MyWTraced

-- Example/computation-related things

instance BaseType Int where
instance Key Int where
  nullKey   = -1
  isNullKey = (== nullKey)

data MySet = Tails | Heads deriving (Eq, Show, Typeable)
instance BaseType MySet where
myNot :: MySet -> MySet
myNot Tails = Heads
myNot Heads = Tails

input :: (Key key, Distr distr) => GenVal key distr MyElt MySet
input = ret $ MyElt Tails
input' :: Distr distr => GenVal Int distr MyElt MySet
input' = Sample (0 :: Int)
                (dirac $ MyElt Tails)
                (\(MyElt x) -> if x == Tails then 1.0 else 0.0)

drunkenNotList :: (Fractional t) => MySet -> [(MyElt MySet, t)]
drunkenNotList x = [(MyElt $ myNot x, 0.9), (MyElt x, 0.1)]
drunkenNotScore :: MySet -> MyElt MySet -> Double
drunkenNotScore x (MyElt y) = if y == x then 0.1 else 0.9
drunkenNot :: (Key key, Distr distr) =>
              (MySet -> distr MyElt MySet) -> key ->
              GenFn key distr MyElt MySet MySet
drunkenNot d k = Gen $ \(MyElt x) ->
                         Sample k (d x) (drunkenNotScore x)

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
  let yws  = squashDiracs xvs
      hit  = filter (\(y, _) -> y == x) yws
      miss = filter (\(y, _) -> y /= x) yws
  in if null hit then (x, v) : yws
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
  dirac x       = Diracs [(x, 1.0)]
  mixture d1 d2 = Diracs . squashDiracs . concat $
    map (\(x, u) -> map (\(y, v) -> (y, u * v)) (diracs $ d2 x))
        (diracs d1)

tracing1 = tracing :: GenVal Int Diracs MyElt MySet ->
                      GenVal Int Diracs (MyTraced Int) MySet
infer1 = infer :: MyTrace Int -> GenVal Int Diracs MyElt MySet ->
                  GenVal Int Diracs (MyWTraced Int) MySet

input1 = input :: GenVal Int Diracs MyElt MySet
input1' = input' :: GenVal Int Diracs MyElt MySet
drunkenNot1 = drunkenNot $ Diracs . drunkenNotList
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

tracing2 = tracing :: GenVal Int DSampler MyElt MySet ->
                      GenVal Int DSampler (MyTraced Int) MySet
infer2 = infer :: MyTrace Int -> GenVal Int DSampler MyElt MySet ->
                  GenVal Int DSampler (MyWTraced Int) MySet

input2 = input :: GenVal Int DSampler MyElt MySet
input2' = input' :: GenVal Int DSampler MyElt MySet
-- This is especially not stochastic:
drunkenNot2 = drunkenNot $ MDistr . \x () -> MyElt $ myNot x
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
drunkenNot3 = drunkenNot $ MDistr . fromList . drunkenNotList
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
  print $ fromIntegral (length tails) / fromIntegral n

-- try:
-- > rsample . runGen $ computed3
-- > rsample . runGen $ computed3'
-- > rsample . runGen $ computed3''
-- > rsample . runGen $ computed3'''
-- > rsample . runGen $ tracing3 computed3
-- > rsample . runGen $ tracing3 computed3'
-- > rsample . runGen $ infer3 tObs computed3'
-- ...
-- > test3 100

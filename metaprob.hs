-- Helpers
enumValues :: (Enum a) => [a]
enumValues = enumFrom (toEnum 0)
test :: (Eq a) => a -> a -> b -> b -> b
test x y u v = if x == y then u else v

-- Plays the role of A x Trace in the paper, where A = values
data Traced keys values = Traced
  { val :: values
  , tr :: [(keys,String)] }
instance (Eq keys, Eq values) => Eq (Traced keys values) where
  xs == yt = val xs == val yt && tr xs == tr yt
instance (Enum keys, Enum values) => Enum (Traced keys values) where
  toEnum = undefined
  fromEnum = undefined
instance Functor (Traced keys) where
  fmap f t = Traced (f $ val t) (tr t)

-- Operations we need to be able to perform on distributions in order
-- to implement operations on generative functions
class DistrOps distrs where
  -- Needed for runGen
  dirac :: (Eq elts) => elts -> distrs elts
  convolve :: (Enum elts) =>
              (distrs elts) -> (elts -> distrs elts) -> distrs elts
  -- Needed for runTracing
  traceless :: (distrs elts) -> distrs (Traced keys elts)

data Samplable distrs elts = Samplable
  { sample :: distrs elts
  , score :: elts -> Double }

data GenFn keys distrs elts =
  Sample keys (Samplable distrs elts) |
  Ret elts |
  Semicolon (GenFn keys distrs elts) (elts -> GenFn keys distrs elts)

runGen :: (Eq elts, Enum elts, DistrOps distrs) =>
          (GenFn keys distrs elts) -> distrs elts
runGen (Sample key dist) = sample dist
runGen (Ret elt) = dirac elt
runGen (Semicolon p1 p2) = convolve (runGen p1) (runGen . p2)

runTracing :: (Eq elts, Enum elts, Show elts, DistrOps distrs) =>
  (GenFn keys distrs elts) -> GenFn keys distrs (Traced keys elts)
runTracing (Sample key dist) = Semicolon
  (Sample key $ Samplable (traceless $ sample dist) ((score dist) . val))
  (\xt -> Ret $ Traced (val xt) [(key, show $ val xt)])
runTracing (Ret elt) = Ret $ Traced elt []
runTracing (Semicolon p1 p2) =
  Semicolon
    (runTracing p1)
    (\xs -> Semicolon
      (runTracing (p2 (val xs)))
      (\yt -> Ret $ Traced (val yt) ((tr xs) ++ (tr yt)) ))

-- Meta-example
data Distrs elts = Distr { mu :: elts -> Double }
instance DistrOps Distrs where
  dirac elt = Distr (\elt' -> test elt elt' 1.0 0.0)
  convolve d1 d2 =
    Distr (\elt' ->
      sum $ map (\elt -> ((mu (d2 elt)) elt') * ((mu d1) elt)) enumValues)
  traceless distr = Distr (\xt ->
    if null (tr xt) then (mu distr) (val xt) else 0.0)

-- Infra-example:
-- All the unknown random state consists of a single coin toss outcome.
data MySet = Tails | Heads deriving (Show, Eq, Enum)
mySet = [Tails, Heads]
makeSamplable f = Samplable (Distr f) f

input = Ret Tails
input2Elems Tails = 0.8
input2Elems Heads = 0.2
input2 = Sample 0 $ makeSamplable input2Elems
drunkenNot key x = Sample key $ makeSamplable (\y -> test x y 0.1 0.9)
computed = Semicolon (Semicolon input (drunkenNot 1)) (drunkenNot 2)
computed2 = Semicolon (Semicolon input2 (drunkenNot 1)) (drunkenNot 2)

debugGen :: (Distrs MySet) -> String
debugGen d =
  "Tails: " ++ (show $ (mu d) Tails) ++ ", Heads: " ++ (show $ (mu d) Heads)

debugTrace :: (Distrs (Traced Integer MySet)) -> String
debugTrace d =
  "  Tails: " ++ (show $ mu d $ Traced Tails []) ++
  ", Heads: " ++ (show $ mu d $ Traced Heads [])

-- try:
-- debugGen $ runGen computed
-- debugTrace $ runGen $ runTrace $ computed

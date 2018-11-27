
{-# LANGUAGE FunctionalDependencies #-}

newtype Distribution subsets = Distribution
  { mu :: subsets -> Double }

newtype Derivative elements = Derivative
  { nu :: elements -> Double}

data DDistribution elements subsets = DDistribution
  { sample :: Distribution subsets
  , score :: Derivative elements }

data GenerativeFunction keys elements subsets =
  Sample keys (DDistribution elements subsets) |
  Ret elements |
  Semicolon
    (GenerativeFunction keys elements subsets)
    (elements -> GenerativeFunction keys elements subsets)

-- These are the structures required to define runGen.
-- Note: If Distribution satisfies
--   Distribution subsets === m elements
-- where m is a monad, then we get a measure space instance via
--   dirac = return
--   convolve = bind
class MeasureSpace elements subsets | subsets -> elements where
  dirac :: elements -> Distribution subsets
  convolve ::
    (Distribution subsets) ->
    (elements -> Distribution subsets) ->
    Distribution subsets

runGen :: (MeasureSpace elements subsets) =>
  (GenerativeFunction keys elements subsets) ->
  Distribution subsets
runGen (Sample key dist) = sample dist
runGen (Ret e) = dirac e
runGen (Semicolon p1 p2) = convolve (runGen p1) (runGen . p2)


-- Meta-example
-- If everything :: [a] is finite with distinct elements, then it
-- determines a uniform probability space.  The elements of this space
-- are the objects UE (everything,e) where e `elem` everything.  The
-- subsets of this space, all deemed measurable, correspond to objects
-- US (everything,s) where s is a subset of the elements of
-- everything, made into a list using the ordering implicit in
-- everything.
data UniformElements a = UE { ue :: ([a],a) }
data UniformSubsets a = US { us :: ([a],[a]) }
instance (Eq a) =>
         MeasureSpace (UniformElements a) (UniformSubsets a) where
  dirac e = Distribution (\s ->
    if (snd (ue e)) `elem` (snd (us s)) then 1.0 else 0.0)
  convolve d1 d2 = Distribution (\u  ->
    let (everything,subset) = us u in
    sum $ map
      (\y -> sum $ map
        (\x ->
           ((mu (d2 (UE (everything,x)))) (US (everything,[y])))
           * ((mu d1) (US (everything,[x]))))
        everything)
      subset)
-- Helpers
fromElements atElem = Distribution (\u ->
  let (everything,subset) = us u in
  sum $ map (\x -> atElem (UE (everything,x))) subset)
toElements d e = let (everything,element) = ue e in
  (mu d) $ US (everything,[element])

-- Infra-example:
-- All the unknown random state consists of a single coin toss outcome.
data MySet = Tails | Heads deriving (Show, Ord, Eq)
mySet = [Tails, Heads]

initialKnowledge = Ret $ UE (mySet, Tails)
initialKnowledge2Elems (UE (everything,Tails)) = 0.8
initialKnowledge2Elems (UE (everything,Heads)) = 0.2
initialKnowledge2Dist =
  DDistribution
    (fromElements initialKnowledge2Elems)
    (Derivative initialKnowledge2Elems)
initialKnowledge2 = Sample 0 $ initialKnowledge2Dist

drunkenNotBase :: (UniformElements MySet) -> (UniformSubsets MySet) -> Double
drunkenNotBase _              (US (_,[]))            = 0.0
drunkenNotBase (UE (_,Tails)) (US (_,[Heads]))       = 0.9
drunkenNotBase (UE (_,Tails)) (US (_,[Tails]))       = 0.1
drunkenNotBase (UE (_,Tails)) (US (_,[Tails,Heads])) = 1.0
drunkenNotBase (UE (_,Heads)) (US (_,[Tails]))       = 0.9
drunkenNotBase (UE (_,Heads)) (US (_,[Heads]))       = 0.1
drunkenNotBase (UE (_,Heads)) (US (_,[Tails,Heads])) = 1.0
drunkenNot ::
  key -> (UniformElements MySet) ->
  GenerativeFunction key (UniformElements MySet) (UniformSubsets MySet)
drunkenNot key x =
  let f = Distribution (\u -> drunkenNotBase x u) in
    Sample key (DDistribution f (Derivative (toElements f)))

computedKnowledge =
  Semicolon (Semicolon initialKnowledge (drunkenNot 1)) (drunkenNot 2)
computedKnowledge2 =
  Semicolon (Semicolon initialKnowledge2 (drunkenNot 1)) (drunkenNot 2)

debug :: (Distribution (UniformSubsets MySet)) -> String
debug d =
  "Tails: " ++ (show $ (mu d) (US (mySet,[Tails]))) ++ ", Heads: " ++ (show $ (mu d) (US (mySet,[Heads])))
-- try: debug $ runGen computedKnowledge

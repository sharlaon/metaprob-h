-- We model probability theory (deterministically, for now) via
-- operations on measure spaces.

-- Notation:
--   a is the type "A" in the paper,
--     i.e. the set of atomic events,
--   pa is the set of all events of type a,
--     i.e. the measurable subsets of a, and
--   base is a fixed probability measure on a
-- Assumed: (memberof x $ singleton y) === (x == y)
data MeasureSpace a pa = MeasureSpace {
  singleton :: a -> pa,
  memberof :: a -> pa -> Bool,
  base :: pa -> Double,
  convolve ::
    (pa -> Double) -> (pa -> pa -> Double) -> (pa -> Double) }

-- Notation:
--   sample and score are as in the paper.  For a distribution mu,
--   sample(U) = \int_U 1 d(mu), and
--   score is the Radon--Nikodym derivative of mu w.r.t. (base meas)
-- (See the finite case for more info on the latter.)
data Distribution a pa =
  Distribution { sample :: pa -> Double, score :: a -> Double }

-- Yes, we are carrying around baggage of the measure space / domain;
-- this aspect will be improved upon later.
-- Notation as otherwise in the paper.
-- (Note that in the paper "p2 :: P(A)", but this is inaccurate.
-- Instead "p2 :: P(A times A)" or "p2 :: A -> P(A)".  We follow the
-- latter possibility here.)
data GenerativeFunction key a pa =
  Ret (MeasureSpace a pa) a |
  Sample (MeasureSpace a pa) key (Distribution a pa) |
  Semicolon (MeasureSpace a pa) (GenerativeFunction key a pa) (pa -> GenerativeFunction key a pa)

delta_measure :: MeasureSpace a pa -> a -> pa -> Double
delta_measure meas x u
  | memberof meas x u = 1.0
  | otherwise         = 0.0
-- Not presently used, and is the only place where Eq is required.
-- delta_score :: (Eq a) => a -> a -> Double
-- delta_score x y
--   | x == y    = 1.0
--   | otherwise = 0.0
-- delta_distribution :: (Eq a) =>
--   (MeasureSpace a pa) -> a -> (Distribution a pa)
-- delta_distribution meas x =
--   Distribution (delta_measure meas x) (delta_score x)

runGen :: GenerativeFunction key a pa -> pa -> Double
runGen (Ret meas x) = delta_measure meas x
runGen (Sample _ _ s) = sample s
runGen (Semicolon meas p1 p2) =
  convolve meas (runGen p1) (\u v -> runGen (p2 u) v)


-- Assume in this comment block that
--   a is finite
--   pa = the power set of a
--   base is nondegenerate on a:
--     base . singleton is nonvanishing
-- Hence the notation "pa"!
--
-- Fix an ordering on the set of elements of a, and denote
--   everything = [elts of a, in order]
-- Also assume two mutually inverse functions
--   toList, fromList
-- that exchange values :: pa with ordered lists of values :: a.  Thus,
--   toList u = filter (`memberof` u) everything
--   toList $ singleton x = [x]
--
-- The "uniform" case means that
--   base . singleton
--     === const $ recip . fromIntegral $ length everything
-- but only nondegeneracy is assumed.
--
-- A function d :: pa -> Double is then a distribution when it satisfies
--   d u === sum $ map (d . singleton) $ toList u
-- The nondegeneracy of base means that every distribution is
-- absolutely continuous, and we may construct its Radon--Nikodym
-- derivative (== PDF when mu is a probability measure):
--   toDeriv :: (pa -> Double) -> a -> Double
--   toDeriv d x = (d $ singleton x) / (base $ singleton x)
-- as well as invert the construction:
--   fromDeriv :: (a -> Double) -> pa -> Double
--   fromDeriv deriv u =
--     sum $ map (\x -> (deriv x) * (base $ singleton x)) $ toList u
--
-- Under these assumptions, the "correct" convolve satisfies
--   convolve d1 d2 $ singleton y ===
--     sum $ map (\x ->
--         (d2 (singleton x) (singleton y)) * (d1 $ singleton x)
--       ) everything


uniformSpace :: (Eq a) => [a] -> MeasureSpace a [a]
uniformSpace everything =
  MeasureSpace singleton memberof base convolve
  where
    singleton = (:[])
    memberof = elem
    base = const $ recip . fromIntegral $ length everything
    convolve d1 d2 u =
      sum $ map (\y ->
        sum $ map (\x -> (d2 [x] [y]) * (d1 [x])) everything) u
toDeriv :: (MeasureSpace a pa) -> (pa -> Double) -> a -> Double
toDeriv meas d x = (d $ singleton meas x) / (base meas $ singleton meas x)
-- We cheat a little bit here:
fromDeriv :: (MeasureSpace a [a]) -> (a -> Double) -> [a] -> Double
fromDeriv meas deriv u =
  sum $ map (\x -> (deriv x) * (base meas $ singleton meas x)) u

-- Example:
-- All the unknown random state consists of a single coin toss outcome.
data MySampleSpace = Tails | Heads deriving (Show, Ord, Eq)
myMeas = uniformSpace [Tails, Heads]


debug :: ([MySampleSpace] -> Double) -> String
debug d =
  "Tails: " ++ (show $ d [Tails]) ++ ", Heads: " ++ (show $ d [Heads])

initialKnowledge = Ret myMeas Tails

initialKnowledge2Deriv :: MySampleSpace -> Double
initialKnowledge2Deriv Tails = 0.8
initialKnowledge2Deriv Heads = 0.2
initialKnowledge2 =
  Sample myMeas 0 $
    Distribution (fromDeriv myMeas initialKnowledge2Deriv) initialKnowledge2Deriv

drunkenNotBase :: [MySampleSpace] -> [MySampleSpace] -> Double
drunkenNotBase []      _       = 0.0
drunkenNotBase _       []      = 0.0
drunkenNotBase [Tails] [Heads] = 0.9
drunkenNotBase [Tails] [Tails] = 0.1
drunkenNotBase [Tails] [Tails,Heads] = 1.0
drunkenNotBase [Heads] [Tails] = 0.9
drunkenNotBase [Heads] [Heads] = 0.1
drunkenNotBase [Heads] [Tails,Heads] = 1.0
drunkenNotBase [Tails,Heads] [Tails,Heads] = 2.0
drunkenNot ::
  key -> [MySampleSpace] ->
    GenerativeFunction key MySampleSpace [MySampleSpace]
drunkenNot key x =
  let f y = drunkenNotBase x y in
    Sample myMeas key (Distribution f (toDeriv myMeas f))

computedKnowledge = 
  Semicolon myMeas (
    Semicolon myMeas initialKnowledge (drunkenNot 1)) (drunkenNot 2)
computedKnowledge2 = 
  Semicolon myMeas (
    Semicolon myMeas initialKnowledge2 (drunkenNot 1)) (drunkenNot 2)
-- try: debug $ runGen computedKnowledge

{-# LANGUAGE RecordWildCards, LambdaCase #-}
module Wang where

import Data.Monoid
import Control.Newtype
import Data.List

humpty :: (Newtype n o, Monoid o) => n
humpty = pack mempty

(<^^>) :: (Newtype n o, Monoid o) => n -> n -> n
x <^^> y = pack (unpack x <> unpack y)

data Fmla
  = V Int
  | F
  | Fmla :\/: Fmla
  | T
  | Fmla :/\: Fmla
  | N Fmla
  deriving Show

data Anxiety
  = Chill  -- there is no need to worry in this subcase
  | Yikes  -- we're indiscriminately stuffed in this subcase
  | Split Anxiety Int Anxiety -- this case matters
      -- left go the countermodels in which the var is a hypo
      -- right go the countermodels in which the var is a goal
      -- all splits, left and right, are on strictly higher vars

instance Show Anxiety where
  show Chill = "Always"
  show Yikes = "Never"
  show a = "Except for " ++ intercalate ", or " (map mo (go a)) where
    go Chill = []
    go Yikes = [([], [])]
    go (Split h i g) =
      [(i : hs, gs) | (hs, gs) <- go h] ++
      [(hs, i : gs) | (hs, gs) <- go g]
    mo (hs, []) = "all of " ++ show hs
    mo ([], gs) = "none of " ++ show gs
    mo (hs, gs) = show hs ++ " but not " ++ show gs

instance Eq Anxiety where
  Chill == Chill = True
  Yikes == Yikes = True
  Split hi i gi == Split hj j gj  -- test the vars first!
    = i == j && hi == hj && gi == gj
  _ == _ = False

split :: Anxiety -> Int -> Anxiety -> Anxiety
split h i g
  | obvEq h g = h  -- if the countermodels match, no need to split
  | otherwise = Split h i g
  where
  obvEq Chill Chill = True
  obvEq Yikes Yikes = True
  {-
  -- is it worth it?
  obvEq (Split hi i gi) (Split hj j gj) =
    i == j && obvEq hi hj && obvEq gi gj
  -}
  obvEq _ _ = False

instance Semigroup Anxiety where (<>) = mappend
instance Monoid Anxiety where
  -- we're collating countermodels
  mempty = Chill
  -- Chill is absorbed
  mappend Chill b = b
  mappend a Chill = a
  -- Yikes dominates
  mappend Yikes b = Yikes
  mappend a Yikes = Yikes
  -- otherwise, do the merge-like thing
  mappend a@(Split hi i gi) b@(Split hj j gj) = case compare i j of
    LT -> split (hi <> b) i (gi <> b)
    EQ -> split (hi <> hj) i (gi <> gj)
    GT -> split (a <> hj) j (a <> gj)

hypo :: Int -> Anxiety -> Anxiety
hypo i Chill = Chill
hypo i Yikes = Split Yikes i Chill
hypo i a@(Split h j g) = case compare i j of
  LT -> split a i Chill
  EQ -> split h i Chill
  GT -> split (hypo i h) j (hypo i g)

goal :: Int -> Anxiety -> Anxiety
goal i Chill = Chill
goal i Yikes = Split Chill i Yikes
goal i a@(Split h j g) = case compare i j of
  LT -> split Chill i a
  EQ -> split Chill i g
  GT -> split (goal i h) j (goal i g)

chillOut :: Endo Anxiety -> Endo Anxiety
chillOut (Endo f) = Endo $ \case
  Chill -> Chill
  a     -> f a

wang, wang', gnaw, gnaw' :: Fmla -> Endo Anxiety
wang = chillOut . wang'
wang' (V x)      = Endo (goal x)
wang' F          = mempty
wang' (p :\/: q) = wang p <> wang q
wang' T          = humpty
wang' (p :/\: q) = wang p <^^> wang q
wang' (N p)      = gnaw p
gnaw = chillOut . gnaw'
gnaw' (V x)      = Endo (hypo x)
gnaw' F          = humpty
gnaw' (p :\/: q) = gnaw p <^^> gnaw q
gnaw' T          = mempty
gnaw' (p :/\: q) = gnaw p <> gnaw q
gnaw' (N p)      = wang p

(==>) :: Fmla -> Fmla -> Anxiety
h ==> g = appEndo (wang g <> gnaw h) Yikes


---------------------------

allOf :: [Fmla] -> Fmla
allOf [] = T
allOf [x] = x
allOf (x : xs) = x :/\: allOf xs

someOf :: [Fmla] -> Fmla
someOf [] = F
someOf [x] = x
someOf (x : xs) = x :\/: someOf xs

oneOf :: [Fmla] -> Fmla
oneOf [] = F
oneOf [x] = x
oneOf (x : xs) =
  (x :/\: allOf [N y | y <- xs]) :\/: (N x :/\: oneOf xs)

ham :: [(Int, Int)] -- edges
    -> Fmla
ham es =
  -- every node is in exactly one position
  allOf [oneOf [nodePos i p | p <- [1 .. l]] | i <- ns]
  :/\:
  -- every position has exactly one node
  allOf [oneOf [nodePos i p | i <- ns] | p <- [1 .. l]]  
  :/\:
  -- every edge present is somewhere in the path
  allOf [N (edgeIn x) :\/:
         someOf [(nodePos i p :/\: nodePos j (p + 1)) :\/:
                 (nodePos j p :/\: nodePos i (p + 1))
                | p <- [1 .. l-1]]
        | (x, (i, j)) <- xes]
  :/\:
  -- every step in the path is an edge
  allOf [ someOf [ edgeIn x :/\:
                   ((nodePos i p :/\: nodePos j (p + 1)) :\/:
                    (nodePos j p :/\: nodePos i (p + 1)))
                 | (x, (i, j)) <- xes]
        | p <- [1 .. l-1]]
  where
  xes = zip [0..] es
  e = length es
  ns = nub (es >>= ((pure . fst) <> (pure . snd)))
  n = 10 * (1 + maximum ns)
  l = length ns
  nodePos i p = V (p * n + i)
  edgeIn x = V (n * n + x)

eul :: [(Int, Int)] -- edges
    -> Fmla
eul es =
  -- every edge occurs exactly once
  allOf [oneOf [edgePos e p | p <- [1..l]]
        | (e, (i, j)) <- xes]
  :/\:
  -- every position has exactly one edge
  allOf [oneOf [edgePos e p | (e, _) <- xes]
        | p <- [1..l]]
  :/\:
  allOf [ N (edgePos e 1) :\/: path i 2 :\/: path j 2
        | (e, (i, j)) <- xes]
  where
  xes = zip [0..] es
  l = length xes
  edgePos e p = V (l * p + e)
  path _ p | p >= l = T
  path i p = someOf
    (
    [edgePos e p :/\: path j (p+1) | (e, (q, j)) <- xes, i == q] ++
    [edgePos e p :/\: path j (p+1) | (e, (j, q)) <- xes, i == q]
    )

dual :: [(Int,Int)] -> [(Int,Int)]
dual es = go xes where
  go [] = []
  go ((x, (i, j)) : xes) =
    [(x, y) | (y, (k, l)) <- xes, any (`elem` [k, l]) [i, j]]
    ++ go xes
  xes = zip [0..] es

koenigsberg :: [(Int, Int)]
koenigsberg = [(0,1),(0,1),(0,2),(0,2),(0,3),(1,3),(2,3)]

clique :: Int -> [(Int, Int)]
clique n = go 0 where
  go i | i >= n = []
  go i = [(i, j) | j <- [i+1 .. n-1]] ++ go (i+1)

main :: IO ()
main = print $ eul koenigsberg ==> F

{-# LANGUAGE RecordWildCards, LambdaCase #-}
module Wang where

import Data.Monoid
import Control.Newtype

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
  deriving Show

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
    GT -> split (a <> hj) j (gj <> b)

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

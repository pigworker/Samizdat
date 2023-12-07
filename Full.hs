{-# LANGUAGE DeriveTraversable, FlexibleInstances #-}

module Full where

import Debug.Trace

data Fm' x -- yer maw
  = V x
  | Z
  | D (Fm' x)
  | S (Fm' x)
  | F (Fm' x)
  deriving (Eq, Ord, Functor, Foldable, Traversable)

type Fm = Fm' Int

db :: Fm -> Fm
db Z = Z
db (S f) = S (S (db f))
db f = D f

fu :: Fm -> Fm
fu Z = Z
fu (S f) = S (db (fu f))
fu f = F f

type Store =
  ( Int -- name supply
  , [(Int, Fm)] -- defs var = nm
  )

va :: Int -> Store -> Fm
va x (_ , xns) = case lookup x xns of
  Just n  -> n
  Nothing -> V x

nm :: Fm -> Store -> Fm
nm (V x) ga = va x ga
nm  Z    ga = Z
nm (S f) ga = S (nm f ga)
nm (D f) ga = db (nm f ga)
nm (F f) ga = fu (nm f ga)

sb :: Int -> Fm -> Fm -> Fm
sb x f (V y) = if x == y then f else V y
sb x f  Z    = Z
sb x f (S g) = S (sb x f g)
sb x f (D g) = db (sb x f g)
sb x f (F g) = fu (sb x f g)

gro :: Int -> Fm -> Store -> Store
gro x f (k, xns) = (k, (x, f) : map (sb x f <$>) xns)

occ :: Int -> Fm -> Bool
occ x = any (x ==)

-- Fm is normal
zee :: Fm -> Store -> Maybe Store
zee (V x) ga = pure (gro x Z ga)
zee  Z    ga = Just ga
zee (S _) ga = Nothing
zee (D f) ga = zee f ga
zee (F f) ga = zee f ga

-- Fm is normal
suu :: Fm -> Store -> Maybe (Fm, Store)
suu (V x) (k, xns) = pure (V k, gro x (S (V k)) (k+1, xns))
suu Z ga = Nothing
suu (S f) ga = pure (f, ga)
suu (D f) ga = do
  (g, ga) <- suu f ga
  pure (S (db g), ga)
suu (F f) ga = do
  (g, ga) <- suu f ga
  pure (db (fu g), ga)

-- Fm is normal
evn :: Fm -> Store -> Maybe (Fm, Store)
evn (V x) (k, xns) = pure (V k, gro x (D (V k)) (k+1, xns))
evn Z ga = pure (Z, ga)
evn (S f) ga = do
  (g, ga) <- ood f ga
  pure (S g, ga)
evn (D f) ga = pure (f, ga)
evn (F f) ga = do
  ga <- zee f ga
  pure (Z, ga)

-- Fm is normal
ood :: Fm -> Store -> Maybe (Fm, Store)
ood (V x) (k, xns) = pure (V k, gro x (S (D (V k))) (k+1, xns))
ood Z _ = Nothing
ood (S f) ga = do
  (g, ga) <- evn f ga
  pure (g, ga)
ood (D _) _ = Nothing
ood (F f) ga = do
  (g, ga) <- suu f ga
  pure (fu g, ga)

unify :: Fm -> Fm -> Store -> Maybe Store
unify f g ga = go (nm f ga) (nm g ga) where
  go f g | trace (show f ++ " =? " ++ show g) False = undefined
  go f g | f == g = pure ga
  go f g | f > g  = go g f
  go (V x) g = case occ x g of
    False -> pure (gro x g ga)
    True  -> zee g ga
  go  Z    g = zee g ga
  go (D f) g = do
    (h, ga) <- evn g ga
    unify f h ga
  go (S f) g = do
    (h, ga) <- suu g ga
    unify f h ga
  go (F f) (F g) = go f g
  go _ _ = Nothing

instance Show Fm where
  show f = go (nm f (0, [])) where
    go (V x) = "V" ++ show x
    go Z = "0"
    go (S f) = mo 1 f where
      mo :: Integer -> Fm -> String
      mo k Z = show k
      mo k (S f) = mo (k+1) f
      mo k f = show k ++ "+" ++ go f
    go (D f) = mo 1 f where
      mo :: Integer -> Fm -> String
      mo k (D f) = mo (k+1) f
      mo k f = po k ++ "*" ++ go f
      po i = if length a <= length b then a else b where
        a = show (2 ^ i)
        b = "2^" ++ show i
    go (F f) = "[" ++ go f ++ "]"

instance Num Fm where
  fromInteger 0 = Z
  fromInteger n = S (fromInteger (n - 1))
  Z + f = f
  f + Z = f
  S f + g = S (f + g)
  f + S g = S (f + g)
  D f + D g = db (f + g)
  x + y | x == y = db x
  Z * f = Z
  f * Z = Z
  S f * g = g + (f * g)
  f * S g = f + (f * g)
  D f * g = db (f * g)
  f * D g = db (f * g)
  negate Z = Z
  signum Z = Z
  signum _ = S Z
  abs x = x

{- DIVERGING in VZSDF order, but not VZDSF
unify (S (F (D (V 0)))) (D (F (V 0))) (1, [])
unify (S (F (D (V 0)))) (D (F (V 1))) (2, [])
unify (S (S (S (S (S (D (V 0))))))) (D (D (D (V 1)))) (2, [])
-}
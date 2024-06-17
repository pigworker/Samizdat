{-# LANGUAGE DataKinds, GADTs, KindSignatures, RankNTypes, TypeOperators
  , TypeFamilies
  #-}

module Th where
import Data.Kind


------------------------------------------------------------------------------
-- Equality
------------------------------------------------------------------------------

data (==) :: a -> a -> Type where
  Ry :: x == x


------------------------------------------------------------------------------
-- Natural Numbers
------------------------------------------------------------------------------

data Nat = Z | S Nat deriving Show
data Natty :: Nat -> Type where
  Zy :: Natty Z
  Sy :: Natty n -> Natty (S n)

data Positive :: Nat -> Type where
  Positive :: Natty n -> Positive (S n)


------------------------------------------------------------------------------
-- Thinnings
------------------------------------------------------------------------------

data (<=) :: Nat -> Nat -> Type where
  NN :: n <= m ->   n <= S m
  SS :: n <= m -> S n <= S m
  ZZ ::           Z   <= Z

weeEnd :: n <= m -> Natty n
weeEnd (NN th) =     weeEnd th
weeEnd (SS th) = Sy (weeEnd th)
weeEnd  ZZ     = Zy

bigEnd :: n <= m -> Natty m
bigEnd (NN th) = Sy (bigEnd th)
bigEnd (SS th) = Sy (bigEnd th)
bigEnd  ZZ     = Zy


-- full and empty

io :: Natty n -> n <= n
io  Zy    = ZZ
io (Sy n) = SS (io n)

no :: Natty n -> Z <= n
no  Zy    = ZZ
no (Sy n) = NN (no n)


------------------------------------------------------------------------------
-- Thinnable and Thinning Composition
------------------------------------------------------------------------------

class Thinnable (p :: Nat -> Type) where
  (-<) :: p n -> n <= m -> p m

instance Thinnable ((<=) n) where
  th    -< NN ph = NN (th -< ph)
  NN th -< SS ph = NN (th -< ph)
  SS th -< SS ph = SS (th -< ph)
  ZZ    -< ZZ    = ZZ

-- free thinnability

data (^) :: (Nat -> Type) -> Nat -> Type where
  (:^) :: p n -> n <= m -> p ^ m

instance Thinnable ((^) p) where
  (p :^ th) -< ph = p :^ (th -< ph)


------------------------------------------------------------------------------
-- Antisymmetry
------------------------------------------------------------------------------

dropLast :: S n <= m -> n <= m
dropLast (SS th) = NN th
dropLast (NN th) = NN (dropLast th)

noBig :: S n <= n -> x
noBig (NN th) = noBig (dropLast th)
noBig (SS th) = noBig th

antisym :: n <= m -> m <= n -> n == m
antisym (NN th)     ph  = noBig (ph -< th)
antisym     th  (NN ph) = noBig (th -< ph)
antisym (SS th) (SS ph) = case antisym th ph of Ry -> Ry
antisym  ZZ      ZZ     = Ry


------------------------------------------------------------------------------
-- Unions
------------------------------------------------------------------------------

data Union :: Nat -> Nat -> Nat -> Type where
  NSS :: Union l r n -> Union    l  (S r) (S n)
  SNS :: Union l r n -> Union (S l)    r  (S n)
  SSS :: Union l r n -> Union (S l) (S r) (S n)
  ZZZ :: Union Z Z Z

luth :: Union l r n -> l <= n
luth (NSS u) = NN (luth u)
luth (SNS u) = SS (luth u)
luth (SSS u) = SS (luth u)
luth  ZZZ    = ZZ

ruth :: Union l r n -> r <= n
ruth (NSS u) = SS (ruth u)
ruth (SNS u) = NN (ruth u)
ruth (SSS u) = SS (ruth u)
ruth  ZZZ    = ZZ

cop :: l <= m -> r <= m -> Union l r ^ m
cop (NN th) (NN ph) = case cop th ph of u :^ ps ->     u :^ NN ps
cop (NN th) (SS ph) = case cop th ph of u :^ ps -> NSS u :^ SS ps
cop (SS th) (NN ph) = case cop th ph of u :^ ps -> SNS u :^ SS ps
cop (SS th) (SS ph) = case cop th ph of u :^ ps -> SSS u :^ SS ps
cop  ZZ      ZZ     = ZZZ :^ ZZ

allLeft :: Natty n -> Union n Z n
allLeft  Zy    = ZZZ
allLeft (Sy n) = SNS (allLeft n)

noneRight :: Union l Z n -> l == n
noneRight (SNS u) = case noneRight u of Ry -> Ry
noneRight  ZZZ    =                           Ry

flipU :: Union l r n -> Union r l n
flipU (NSS u) = SNS (flipU u)
flipU (SNS u) = NSS (flipU u)
flipU (SSS u) = SSS (flipU u)
flipU  ZZZ    = ZZZ

allRight :: Natty n -> Union Z n n
allRight = flipU . allLeft

noneLeft :: Union Z r n -> r == n
noneLeft = noneRight . flipU

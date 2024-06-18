{-# LANGUAGE DataKinds, GADTs, TypeOperators, KindSignatures, RankNTypes, QuantifiedConstraints, ConstraintKinds #-}

module Thin where

data (x :: a) :=: (y :: a) where
  Refl :: x :=: x

class IxEq (p :: a -> *) where
  (=?=) :: p x -> p y -> Maybe (x :=: y)

data Nat = Z | S Nat

instance Show Nat where
  show = show . count where
    count :: Nat -> Int
    count Z = 0
    count (S n) = 1 + count n

type Shown (p :: Nat -> *) = forall n. Show (p n)

data Natty (n :: Nat) where
  Zy :: Natty Z
  Sy :: Natty n -> Natty (S n)

instance Show (Natty n) where
  show = show . count where
    count :: forall n. Natty n -> Int
    count Zy = 0
    count (Sy n) = 1 + count n

instance IxEq Natty where
  Zy   =?= Zy   = pure Refl
  Sy n =?= Sy m = do
    Refl <- n =?= m
    pure Refl
  _    =?= _    = Nothing

data (n :: Nat) <= (m :: Nat) :: * where
  IS :: n <= m ->   n <= S m
  SS :: n <= m -> S n <= S m
  ZZ :: Z <= Z

instance Show (n <= m) where
  show th = concat ["|", go th, "|"] where
    go :: forall n m. n <= m -> String
    go (IS th) = go th ++ "0"
    go (SS th) = go th ++ "1"
    go ZZ = ""

bigEnd :: n <= m -> Natty m
bigEnd (IS th) = Sy (bigEnd th)
bigEnd (SS th) = Sy (bigEnd th)
bigEnd  ZZ     = Zy

weeEnd :: n <= m -> Natty n
weeEnd (IS th) =     weeEnd th
weeEnd (SS th) = Sy (weeEnd th)
weeEnd  ZZ     = Zy

thinEqEh :: a <= b -> c <= d -> Maybe (a :=: c, b :=: d)
thinEqEh (IS th) (IS ph) = do (Refl, Refl) <- thinEqEh th ph; pure (Refl, Refl)
thinEqEh (SS th) (SS ph) = do (Refl, Refl) <- thinEqEh th ph; pure (Refl, Refl)
thinEqEh  ZZ      ZZ     =                                    pure (Refl, Refl)
thinEqEh     _       _   = Nothing

class Thinny (p :: Nat -> *) where
  (-<) :: p n -> n <= m -> p m
infixl 5 -<

instance Thinny ((<=) n) where
  th    -< IS ph = IS (th -< ph)
  IS th -< SS ph = IS (th -< ph)
  SS th -< SS ph = SS (th -< ph)
  ZZ    -< ZZ    = ZZ

instance Thinny Natty where
  n    -< IS th = Sy (n -< th)
  Sy n -< SS th = Sy (n -< th)
  Zy   -< ZZ    = Zy

io :: Natty n -> n <= n
io Zy = ZZ
io (Sy n) = SS (io n)

data CdB (p :: Nat -> *) (m :: Nat) :: * where
  (:^) :: p n -> n <= m -> CdB p m
infixl 4 :^

instance Shown p => Show (CdB p n) where
  show (p :^ th) = concat ["(", show p, " :^", show th, ")"]

instance Thinny (CdB p) where
  (p :^ th) -< ph = p :^ th -< ph

no :: Natty n -> Z <= n
no  Zy    = ZZ
no (Sy n) = IS (no n)

data Cov (l :: Nat)(r :: Nat)(m :: Nat) :: * where
  SIS :: Cov l r n -> Cov (S l)    r  (S n)
  ISS :: Cov l r n -> Cov    l  (S r) (S n)
  SSS :: Cov l r n -> Cov (S l) (S r) (S n)
  ZZZ :: Cov Z Z Z

lCov :: Cov l r n -> l <= n
lCov (SIS th) = SS (lCov th)
lCov (ISS th) = IS (lCov th)
lCov (SSS th) = SS (lCov th)
lCov  ZZZ     = ZZ

rCov :: Cov l r n -> r <= n
rCov (SIS th) = IS (rCov th)
rCov (ISS th) = SS (rCov th)
rCov (SSS th) = SS (rCov th)
rCov  ZZZ     = ZZ

lSup :: Cov l r n -> Natty l
lSup u = weeEnd (lCov u)

rSup :: Cov l r n -> Natty r
rSup u = weeEnd (rCov u)

instance Show (Cov l r n) where
  show u = concat ["<", show (lCov u), show (rCov u), ">"]

cop :: l <= m -> r <= m -> CdB (Cov l r) m
cop (IS th) (IS ph) = case cop th ph of u :^ ps ->     u :^ IS ps
cop (SS th) (IS ph) = case cop th ph of u :^ ps -> SIS u :^ SS ps
cop (IS th) (SS ph) = case cop th ph of u :^ ps -> ISS u :^ SS ps
cop (SS th) (SS ph) = case cop th ph of u :^ ps -> SSS u :^ SS ps
cop  ZZ      ZZ     =                              ZZZ   :^ ZZ

covL :: Natty n -> Cov n Z n
covL  Zy    = ZZZ
covL (Sy n) = SIS (covL n)

allLeft :: Cov l Z n -> l :=: n
allLeft (SIS u) = case allLeft u of
  Refl -> Refl
allLeft  ZZZ    = Refl

covR :: Natty n -> Cov Z n n
covR  Zy    = ZZZ
covR (Sy n) = ISS (covR n)

allRight :: Cov Z r n -> r :=: n
allRight (ISS u) = case allRight u of
  Refl -> Refl
allRight  ZZZ    = Refl

covLR :: Natty n -> Cov n n n
covLR  Zy    = ZZZ
covLR (Sy n) = SSS (covLR n)

swapCov :: Cov l r n -> Cov r l n
swapCov (ISS u) = SIS (swapCov u)
swapCov (SIS u) = ISS (swapCov u)
swapCov (SSS u) = SSS (swapCov u)
swapCov  ZZZ    = ZZZ

data RotRCov a b c abc where
  RotRCov :: Cov a bc abc -> Cov b c bc -> RotRCov a b c abc

rotRCov :: Cov a b ab -> Cov ab c abc -> RotRCov a b c abc
rotRCov      u  (ISS w) = case rotRCov u w of RotRCov w' u' -> RotRCov (ISS w') (ISS u')
rotRCov (ISS u) (SIS w) = case rotRCov u w of RotRCov w' u' -> RotRCov (ISS w') (SIS u')
rotRCov (SIS u) (SIS w) = case rotRCov u w of RotRCov w' u' -> RotRCov (SIS w')      u'
rotRCov (SSS u) (SIS w) = case rotRCov u w of RotRCov w' u' -> RotRCov (SSS w') (SIS u')
rotRCov (ISS u) (SSS w) = case rotRCov u w of RotRCov w' u' -> RotRCov (ISS w') (SSS u')
rotRCov (SIS u) (SSS w) = case rotRCov u w of RotRCov w' u' -> RotRCov (SSS w') (ISS u')
rotRCov (SSS u) (SSS w) = case rotRCov u w of RotRCov w' u' -> RotRCov (SSS w') (SSS u')
rotRCov  ZZZ     ZZZ    = RotRCov ZZZ ZZZ

data RotLCov a b c abc where
  RotLCov :: Cov a b ab -> Cov ab c abc -> RotLCov a b c abc

rotLCov :: Cov a bc abc -> Cov b c bc -> RotLCov a b c abc
rotLCov u w = case rotRCov (swapCov w) (swapCov u) of
  RotRCov u' w' -> RotLCov (swapCov w') (swapCov u')

data Mid4Cov a b c d n where
  Mid4Cov :: Cov a c ac -> Cov ac bd n -> Cov b d bd -> Mid4Cov a b c d n

mid4Cov :: Cov a b ab -> Cov ab cd n -> Cov c d cd -> Mid4Cov a b c d n
mid4Cov a_b ab_cd c_d = case rotRCov a_b ab_cd of
  RotRCov a_bcd b_cd -> case rotLCov b_cd c_d of
    RotLCov b_c bc_d -> case rotRCov (swapCov b_c) bc_d of
      RotRCov c_bd b_d -> case rotLCov a_bcd c_bd of
        RotLCov a_c ac_bd -> Mid4Cov a_c ac_bd b_d

data (p :: Nat -> *) ^*^ (q :: Nat -> *) :: Nat -> * where
  Pr :: p l -> Cov l r n -> q r -> (p ^*^ q) n

instance (Shown p, Shown q) => Show ((p ^*^ q) n) where
  show (Pr p u q) = concat ["(", show p , " ", show u, " ", show q, ")"]

infixr 3 ^&^
(^&^) :: CdB p m -> CdB q m -> CdB (p ^*^ q) m
p :^ th ^&^ q :^ ph = case cop th ph of
  u :^ ps -> Pr p u q :^ ps

splip :: CdB (p ^*^ q) m -> (CdB p m, CdB q m)
splip (Pr p u q :^ ps) = (p :^ lCov u -< ps, q :^ rCov u -< ps)

data Un (n :: Nat) :: * where
  Un :: Un Z
instance Show (Un n) where
  show Un = "()"

data Su (p :: Nat -> *) (n :: Nat) where
  La :: p (S n) -> Su p n
  Ka :: p    n  -> Su p n

su :: CdB p (S n) -> CdB (Su p) n
su (p :^ SS th) = La p :^ th
su (p :^ IS th) = Ka p :^ th

us :: CdB (Su p) n -> CdB p (S n)
us (La p :^ th) = p :^ SS th
us (Ka p :^ th) = p :^ IS th

data Span (l :: Nat)(r :: Nat) :: * where
  Span :: n <= l -> n <= r -> Span l r
deriving instance Show (Span l r)

pub :: l <= m -> r <= m -> Span l r
pub (IS th) (IS ph) = pub th ph
pub (IS th) (SS ph) = case pub th ph of Span th' ph' -> Span     th'  (IS ph')
pub (SS th) (IS ph) = case pub th ph of Span th' ph' -> Span (IS th')     ph'
pub (SS th) (SS ph) = case pub th ph of Span th' ph' -> Span (SS th') (SS ph')
pub  ZZ      ZZ     =                                   Span  ZZ       ZZ

ioEh :: n <= m -> Maybe (n :=: m)
ioEh th = weeEnd th =?= bigEnd th

subThinEh :: l <= m -> n <= m -> Maybe (l <= n)
subThinEh th ph = case pub th ph of Span th' ph' -> do Refl <- ioEh th'; pure ph'
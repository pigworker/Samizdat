{-# LANGUAGE DataKinds, GADTs, TypeFamilies, TypeOperators, StandaloneDeriving, QuantifiedConstraints, UndecidableInstances #-}

module Term where

import Thin

data TmSort = Syn | Chk deriving Show

data TmSorty (t :: TmSort) :: * where
  Syny :: TmSorty Syn
  Chky :: TmSorty Chk

data Sort
  = Term TmSort
  | Bind Sort
  | Pair Sort Sort
  | Unit
  | Vect Nat Sort
  deriving Show

data Sorty (s :: Sort) :: * where
  Termy :: TmSorty t -> Sorty (Term t)
  Bindy :: Sorty s -> Sorty (Bind s)
  Pairy :: Sorty l -> Sorty r -> Sorty (Pair l r)
  Unity :: Sorty Unit
  Vecty :: Natty n -> Sorty s -> Sorty (Vect n s)

type family TmOf (s :: Sort) :: Nat -> * where
  TmOf (Term t)       = Tm t
  TmOf (Bind s)       = Su (TmOf s)
  TmOf (Pair l r)     = TmOf l ^*^ TmOf r
  TmOf Unit           = Un
  TmOf (Vect Z s)     = Un
  TmOf (Vect (S n) s) = TmOf (Vect n s) ^*^ TmOf s

data Tm (t :: TmSort) (n :: Nat) :: * where
  (:$)  :: Con s t -> TmOf s n -> Tm t n
  V     :: Tm Syn (S Z)
  A     :: String -> Tm Chk Z

instance Show (Tm t n) where
  show (c :$ t) = concat [ "(", show c, " ", showSort (conSort c) t, ")"] where
  show V        = "#"
  show (A x)    = x

showSort :: forall s n. Sorty s -> TmOf s n -> String
showSort (Bindy s) (Su t)   = concat ["(. ", showSort s t, ")"]
showSort  Unity    _        = "()"
showSort (Pairy l r) (Pr p u q) = concat
  ["(", showSort l p , " ", show u, " ", showSort r q, ")"]
showSort (Termy _)        t = show t
showSort (Vecty  Zy    s) t = showSort Unity t
showSort (Vecty (Sy n) s) t = showSort (Pairy (Vecty n s) s) t

data Con (s :: Sort) (t :: TmSort) :: * where
  Meta :: Name -> Natty n -> Con (Vect n (Term Syn)) Chk
  Abst :: Con (Bind (Term Chk)) Chk
  Cons :: Con (Pair (Term Chk) (Term Chk)) Chk
  Null :: Con Unit Chk
  Turn :: Con (Term Syn) Chk
  Radi :: Con (Pair (Term Chk) (Term Chk)) Syn
  Elim :: Con (Pair (Term Syn) (Term Chk)) Syn
deriving instance Show (Con s t)

conSort :: Con s t -> Sorty s
conSort (Meta _ n) = Vecty n (Termy Syny)
conSort Abst       = Bindy (Termy Chky)
conSort Cons       = Pairy (Termy Chky) (Termy Chky)
conSort Null       = Unity
conSort Turn       = Termy Syny
conSort Radi       = Pairy (Termy Chky) (Termy Chky)
conSort Elim       = Pairy (Termy Syny) (Termy Chky)

sortily :: Sorty s -> (Subst (TmOf s) => r) -> r
sortily (Termy _) k = k
sortily (Bindy s) k = sortily s k
sortily (Pairy l r) k = sortily l (sortily r k)
sortily Unity k = k
sortily (Vecty Zy s) k = k
sortily (Vecty (Sy n) s) k = sortily (Vecty n s) (sortily s k)

type Name = [(String, Int)]

type (/>) (m :: Nat) = TmOf (Vect m (Term Syn))

idSubstEh :: Natty m -> m /> n -> Maybe (m :=: n)
idSubstEh  Zy    Un = pure Refl
idSubstEh (Sy m) (Pr sg (ISS u) V) = case allLeft u of
  Refl -> do
    Refl <- idSubstEh m sg
    pure Refl
idSubstEh  _     _  = Nothing

class Subst (p :: Nat -> *) where
  (//), (///) :: p m -> (Natty m, m /> n, Natty n) -> p n
  p // msg@(m, sg, n) = case idSubstEh m sg of
    Just Refl -> p
    Nothing   -> p /// msg
  
instance Subst (Tm t) where
  (c :$ s) /// msgn                  = sortily (conSort c) (c :$ (s /// msgn))
  V        /// (Sy Zy, Pr Un u e, _) = case allRight u of Refl -> e
  A a      /// (Zy, Un, Zy)          = A a

data Roof (l :: Nat) (r :: Nat) (m :: Nat) (n :: Nat) :: * where
  Roof :: (l /> k) -> Cov k s n -> (r /> s) -> Roof l r m n

roof :: Cov l r m -> m /> n -> Roof l r m n
roof (SSS u) (Pr sg w e) = case roof u sg of
  Roof rh u' ta -> case mid4Cov u' w (covLR (rSup w)) of
    Mid4Cov ul lr ur -> Roof (Pr rh ul e) lr (Pr ta ur e)
roof (ISS u) (Pr sg w e) = case roof u sg of
  Roof rh u' ta -> case rotRCov u' w of
    RotRCov u0 u1 -> Roof rh u0 (Pr ta u1 e)
roof (SIS u) (Pr sg w e) = case roof u sg of
  Roof rh u' ta -> case rotRCov (swapCov u') w of
    RotRCov u0 u1 -> Roof (Pr rh u1 e) (swapCov u0) ta
roof  ZZZ     Un = Roof Un ZZZ Un

instance (Subst p, Subst q) => Subst (p ^*^ q) where
  Pr p u q /// (m, sg, n) = case roof u sg of
    Roof rh w ta -> Pr (p // (lSup u, rh, lSup w)) w (q // (rSup u, ta, rSup w))

instance Subst Un where
  Un /// (Zy, Un, Zy) = Un

instance Subst p => Subst (Su p) where
  Su p /// (m, sg, n) = Su (p /// (Sy m, Pr sg (ISS (covL n)) V, Sy n))

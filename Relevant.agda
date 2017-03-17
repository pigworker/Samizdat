module Relevant where

data Nat : Set where
  ze : Nat
  su : Nat -> Nat

data Fin : Nat -> Set where
  ze : {n : Nat} -> Fin (su n)
  su : {n : Nat} -> Fin n -> Fin (su n)

data OPE : Nat -> Nat -> Set where
  ze : OPE ze ze
  su : {n m : Nat} -> OPE n m -> OPE (su n) (su m)
  no : {n m : Nat} -> OPE n m -> OPE n (su m)

thin : forall {n m} -> OPE n m -> Fin n -> Fin m
thin ze     ()
thin (su r) ze     = ze
thin (su r) (su i) = su (thin r i)
thin (no r) i      = su (thin r i)

idOPE : forall {n} -> OPE n n
idOPE {ze}   = ze
idOPE {su n} = su idOPE

data Tm (n : Nat) : Set where
  va  : Fin n -> Tm n
  _$_ : Tm n -> Tm n -> Tm n
  la  : Tm (su n) -> Tm n

infixl 4 _$_

thinTm : forall {n m} -> OPE n m -> Tm n -> Tm m
thinTm r (va i)  = va (thin r i)
thinTm r (f $ s) = thinTm r f $ thinTm r s
thinTm r (la t)  = la (thinTm (su r) t)

data Zero : Set where
record One : Set where constructor <>

_&_ : forall {n n' m} -> OPE n m -> OPE n' m -> Set
ze   & ze    = One
su r & su r' = r & r'
su r & no r' = r & r'
no r & su r' = r & r'
no r & no r' = Zero

one : Nat -> Set
one (su ze) = One
one _       = Zero

data Re (m : Nat) : Set where
  it : one m -> Re m
  ap : forall {n n'}(r : OPE n m)(r' : OPE n' m) ->
         r & r' -> Re n -> Re n' -> Re m
  la : Re (su m) -> Re m
  ka : Re m -> Re m

reTm : forall {n} -> Re n -> Tm n
reTm {ze} (it ())
reTm {su n} (it i)   = va ze
reTm (ap r r' p f s) = thinTm r (reTm f) $ thinTm r' (reTm s)
reTm (la t)          = la (reTm t)
reTm (ka t)          = la (thinTm (no idOPE) (reTm t))

data RE {m : Nat} : Tm m -> Set where
  mkRE : {n : Nat}(t : Re n)(r : OPE n m) -> RE (thinTm r (reTm t))

re : {n : Nat}(t : Tm n) -> RE t
re t = {!!}

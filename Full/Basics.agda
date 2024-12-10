module Basics where

id : forall {l}{X : Set l} -> X -> X
id x = x

K-_ : forall {k l}{X : Set k}{Y : Set l} -> (x : X)(y : Y) -> X
(K- x) y = x

_-_ : forall {i j k}{A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k}
  (f : (a : A) -> B a)
  (g : {a : A}(b : B a) -> C a b)
  (a : A) -> C a (f a)
(f - g) a = g (f a)
infixl 10 _-_

data _~_ {X : Set}(x : X) : X -> Set where
  r~ : x ~ x
infix 2 _~_
{-# BUILTIN EQUALITY _~_ #-}

sym : forall {X}{x y : X} -> x ~ y -> y ~ x
sym r~ = r~


module _ {X : Set}(x : X) where

  _~[_>_ : forall {y z : X} -> x ~ y -> y ~ z -> x ~ z
  _~[_>_ r~ q = q
  _<_]~_ : forall {y z : X} -> y ~ x -> y ~ z -> x ~ z
  _<_]~_ r~ q = q
  _[QED] : x ~ x
  _[QED] = r~
  infixr 1 _~[_>_ _<_]~_
  infixr 2 _[QED]

_~$~_ : forall {S T}{f g : S -> T} -> f ~ g -> {x y : S} -> x ~ y -> f x ~ f y
r~ ~$~ r~ = r~

_$~_ : forall {S T}(f : S -> T){x y : S} -> x ~ y -> f x ~ f y
f $~ q = (f [QED]) ~$~ q

data Zero : Set where

magic : forall {l}{X : Set l} -> Zero -> X
magic ()

record One : Set where constructor <>

data Two : Set where ff tt : Two

record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_ public
_*_ : Set -> Set -> Set
S * T = S >< \ _ -> T
infixr 10 _,_ _*_

data Nat : Set where
  ze   : Nat
  su-_ : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

NatNoConf : Nat -> Nat -> Set
NatNoConf ze ze = One
NatNoConf ze (su- y) = Zero
NatNoConf (su- x) ze = Zero
NatNoConf (su- x) (su- y) = x ~ y

natNoConf : {x y : Nat} -> x ~ y -> NatNoConf x y
natNoConf {ze} r~ = _
natNoConf {su- x} r~ = r~

_+N_ : Nat -> Nat -> Nat
ze +N y = y
(su- x) +N y = su- (x +N y)

du-_ : Nat -> Nat
du- ze = ze
du- su- n = su- su- du- n

bu-_ : Nat -> Nat
bu- n = su- du- n

fu-_ : Nat -> Nat
fu- ze = ze
fu- su- n = bu- fu- n

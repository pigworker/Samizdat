module StackM where

data Two : Set where ff tt : Two

data Nat : Set where
  ze : Nat
  su : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

_+_ : Nat -> Nat -> Nat
ze + y = y
su x + y = su (x + y)

data _-[_>_ {X : Set}(x : X)(R : X -> X -> Set) : X -> Set where
  [] : x -[ R > x
  _,-_ : forall {y z} -> R x y -> y -[ R > z -> x -[ R > z
infixr 10 _,-_
infix 5 _-[_>_

_++_ : {X : Set}{R : X -> X -> Set}{x y z : X}
    -> x -[ R > y -> y -[ R > z -> x -[ R > z
[]        ++ ss = ss
(r ,- rs) ++ ss = r ,- rs ++ ss
infixr 10 _++_

data Bwd (X : Set) : Set where
  [] : Bwd X
  _-,_ : Bwd X -> X -> Bwd X
infixl 10 _-,_

data Ty : Set where
  `Two : Ty
  `Nat : Ty

Val : Ty -> Set
Val `Two = Two
Val `Nat = Nat

data Inst : Bwd Ty -> Bwd Ty -> Set where
  PSH : forall {Tz T} -> Val T -> Inst Tz (Tz -, T)
  ADD : forall {Tz} -> Inst (Tz -, `Nat -, `Nat) (Tz -, `Nat)
  PAF : forall {Tz Uz}(fc tc : Tz -[ Inst > Uz) -> Inst (Tz -, `Two) Uz

data [Bwd] {X : Set}(P : X -> Set) : Bwd X -> Set where
  []   : [Bwd] P []
  _-,_ : forall {xz x} -> [Bwd] P xz -> P x -> [Bwd] P (xz -, x)

infixl 5 _!>_
_!>_ : forall {Tz Uz} -> [Bwd] Val Tz -> Tz -[ Inst > Uz -> [Bwd] Val Uz
vz !> [] = vz
vz !> PSH x ,- is = vz -, x !> is
vz -, m -, n !> ADD ,- is = vz -, (m + n) !> is
vz -, ff !> PAF fc tc ,- is = vz !> fc !> is
vz -, tt !> PAF fc tc ,- is = vz !> tc !> is


data Expr : Ty -> Set where
  val : {T : Ty} -> Val T -> Expr T
  _+E_ : Expr `Nat -> Expr `Nat -> Expr `Nat
  if_then_else_ : forall {T} -> Expr `Two -> Expr T -> Expr T -> Expr T

eval : forall {T} -> Expr T -> Val T
eval (val x) = x
eval (e +E e') = eval e + eval e'
eval (if eb then et else ef) with eval eb
eval (if eb then et else ef) | ff = eval ef
eval (if eb then et else ef) | tt = eval et

compile : forall {Tz T} -> Expr T -> Tz -[ Inst > Tz -, T
compile (val x) = PSH x ,- []
compile (e +E e') = compile e ++ compile e' ++ ADD ,- []
compile (if e then et else ef) = compile e ++ PAF (compile ef) (compile et) ,- []

data _~_ {X : Set}(x : X) : X -> Set where
  r~ : x ~ x
infix 1 _~_

_~[_>_ : forall {X}(x : X){y z : X} -> x ~ y -> y ~ z -> x ~ z
x ~[ r~ > q = q
_[QED] : forall {X}(x : X) -> x ~ x
x [QED] = r~
infixr 2 _~[_>_
infixr 3 _[QED]

_$~_ : {S T : Set}(f : S -> T){x y : S} -> x ~ y -> f x ~ f y
f $~ r~ = r~

runs : forall {Sz Tz Uz}(vz : [Bwd] Val Sz)(is : Sz -[ Inst > Tz)(js : Tz -[ Inst > Uz)
    -> vz !> is ++ js ~ vz !> is !> js
runs vz [] js = r~
runs vz (PSH x ,- is) js = runs _ is js
runs (vz -, m -, n) (ADD ,- is) js = runs _ is js
runs (vz -, ff) (PAF fc tc ,- is) js = runs _ is js
runs (vz -, tt) (PAF fc tc ,- is) js = runs _ is js

agree : forall {Tz T}(vz : [Bwd] Val Tz)(e : Expr T)
     -> vz !> compile e ~ (vz -, eval e)
agree vz (val x) = r~
agree vz (e +E e') =
  vz !> compile (e +E e')
    ~[ r~ >
  vz !> compile e ++ compile e' ++ ADD ,- []
    ~[ runs vz (compile e) _ >
  vz !> compile e !> compile e' ++ ADD ,- []
    ~[ (_!> compile e' ++ ADD ,- []) $~ agree vz e >
  vz -, eval e !> compile e' ++ ADD ,- []
    ~[ runs (vz -, _) (compile e') _ >
  vz -, eval e !> compile e' !> ADD ,- []
    ~[ (_!> ADD ,- []) $~ agree (vz -, _) e' >
  vz -, eval e -, eval e' !> ADD ,- []
    ~[ r~ >
  (vz -, eval (e +E e'))
    [QED]
agree vz (if e then et else ef) with eval e | agree vz e
agree vz (if e then et else ef) | ff | bq = 
  vz !> compile e ++ PAF (compile ef) (compile et) ,- []
    ~[ runs vz (compile e) _ >
  vz !> compile e !> PAF (compile ef) (compile et) ,- []
    ~[ (_!> PAF (compile ef) (compile et) ,- []) $~ bq >
  vz -, ff !> PAF (compile ef) (compile et) ,- []
    ~[ agree vz ef >
  vz -, eval ef
    [QED]
agree vz (if e then et else ef) | tt | bq =
  vz !> compile e ++ PAF (compile ef) (compile et) ,- []
    ~[ runs vz (compile e) _ >
  vz !> compile e !> PAF (compile ef) (compile et) ,- []
    ~[ (_!> PAF (compile ef) (compile et) ,- []) $~ bq >
  vz -, tt !> PAF (compile ef) (compile et) ,- []
    ~[ agree vz et >
  vz -, eval et
    [QED]


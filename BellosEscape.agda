mutual

  record InfOft (A B : Set) : Set where
    coinductive
    constructor [_]
    field
      gimme : InfOftEra A B

  data InfOftEra (A B : Set) : Set where
    _!-_ : A -> InfOft A B -> InfOftEra A B
    _,-_ : B -> InfOftEra A B -> InfOftEra A B

open InfOft

data Nat : Set where
  ze : Nat
  su : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

data LeftOf (X : Nat -> Set) : Nat -> Set where
  [] : LeftOf X ze
  _<_ : forall {n} -> LeftOf X n -> X n -> LeftOf X (su n)
infixl 5 _<_

record RightFrom (X : Nat -> Set)(i : Nat) : Set where
  coinductive
  constructor _>_
  field
    here : X i
    right : RightFrom X (su i)
open RightFrom
infixr 5 _>_

data Zero : Set where
record One : Set where constructor <>

IsSu : Nat -> Set
IsSu ze = Zero
IsSu (su n) = One

record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg
_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T
infixr 4 _,_ _*_

Signal : Nat -> Set
Signal i = InfOft One (IsSu i)

Position : Set
Position = Sg Nat \ i -> LeftOf Signal i * RightFrom Signal i

step : Position -> Position
step' : forall i -> LeftOf Signal i -> InfOftEra One (IsSu i) -> RightFrom Signal (su i) -> Position
step (i , ls , hrs) with here hrs | right hrs
... | h | rs with gimme h
step (i , ls , hrs)             | h | rs | hi = step' i ls hi rs
step' i ls (x !- h') rs = su i , ls < h' , rs
step' .0 [] (() ,- hi) rs
step' .(su _) (ls < l) (<> ,- hi') rs = _ , ls , l > [ hi' ] > rs

data _~~>_ (p : Position) : Position -> Set where
  stop : p ~~> p
  go_ : forall {p'} ->  step p ~~> p'  ->  p ~~> p'
infixr 5 go_

_++_ : forall {p0 p1 p2 : Position} -> p0 ~~> p1  ->  p1 ~~> p2  ->  p0 ~~> p2
stop ++ qs = qs
(go ps) ++ qs = go (ps ++ qs)
infixr 5 _++_

the : (X : Set) -> X -> X
the X x = x

lemma : forall n ls hrs -> Sg _ \ ls' -> step (n , ls , hrs) ~~> (su n , ls' , right hrs)
lemma n ls hrs with here hrs | right hrs
... | h | r with gimme h
lemma n ls hrs | h | rs | hi = help n ls hi rs where
  help : forall n (ls : LeftOf (λ i → InfOft One (IsSu i)) n)
         (hi : InfOftEra One (IsSu n))
         (rs : RightFrom Signal (su n)) ->
         Sg _ \ ls' -> step' n ls hi rs ~~> (su n , ls' , rs)
  help n ls (<> !- h') rs = _ , stop
  help .0 [] (() ,- hi) rs
  help .(su _) (ls < l) (<> ,- hi) rs with help _ ls (gimme l) ([ hi ] > rs)
  ... | ls' , ps with help _ ls' hi rs
  ... | ls'' , qs = _ , go ps ++ go qs

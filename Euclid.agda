module Euclid where

-- parameters in curly braces are kept implicit by default

-- Equality
data _~_ {X : Set}(x : X) : X -> Set where
  r~ : x ~ x

-- Peano numbers, because speed is overrated
data Nat : Set where
  ze : Nat
  su : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

-- we define addition,, with the intention of doing it backwards
_+N_ : Nat -> Nat -> Nat
ze   +N y = y
su x +N y = su (x +N y)

-- evidence of trichotomy talks about adding
-- and is explicit about positive difference
data Compare : Nat -> Nat -> Set where
  lt : forall {x} d -> Compare x (x +N su d)
  eq : forall {x}   -> Compare x           x
  gt : forall {y} d -> Compare (y +N su d) y

-- we equip any two numbers with comparison evidence
compare : (x y : Nat) -> Compare x y
compare ze ze = eq
compare ze (su y) = lt y
compare (su x) ze = gt x
compare (su x) (su y) with compare x y
compare (su x) (su .(x +N su d)) | lt d = lt d
compare (su x)            (su x) | eq = eq
compare (su .(y +N su d)) (su y) | gt d = gt d

-- evidence for strong inductiveness
data Strong (n : Nat) : Set where
  big : ((x y : Nat) -> n ~ (su x +N y) -> Strong y) -> Strong n

-- we quip every number with strong inductiveness
strong : (n : Nat) -> Strong n
strong ze = big \ _ _ ()
strong (su n) with big h <- strong n = big \ where
  ze y r~ -> big h
  (su x) y r~ -> h x y r~

-- now gcd is defined by recursion on the strong inductiveness
-- of its inputs, analysed by constructive trichotomy
gcdAux : forall x y -> Strong x -> Strong y -> Nat
gcdAux ze y sx sy = y
gcdAux x ze sx sy = x 
gcdAux (su x) (su y) sx sy with compare x y 
gcdAux (su x) (su .(x +N su d)) sx (big sy) | lt d
  = gcdAux (su x) (su d) sx (sy x (su d) r~)
gcdAux (su x) (su x) _ _                    | eq = su x
gcdAux (su .(y +N su d)) (su y) (big sx) sy | gt d
  = gcdAux (su d) (su y) (sx y (su d) r~) sy

-- bibbity bobbity boo
gcd : Nat -> Nat -> Nat
gcd x y = gcdAux x y (strong x) (strong y)

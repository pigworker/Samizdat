module Basics where

id : forall {l}{X : Set l} -> X -> X
id x = x

_-_ : forall {i j k}{A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k}
  (f : (a : A) -> B a)
  (g : {a : A}(b : B a) -> C a b)
  (a : A) ->
  C a (f a)
(f - g) a = g (f a)

data Zero : Set where
record One : Set where constructor <>
data Two : Set where ff tt : Two

record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_ public
_+_ _*_ : Set -> Set -> Set
S + T = Two >< \ { ff -> S ; tt -> T }
S * T = S >< \ _ -> T
pattern !_ t = _ , t
pattern _^_ s t = ! s , t
infixr 20 _+_
infixr 30 _,_ _><_ _*_ !_
infixr 31 _^_

module _ {X : Set} where
  _+:_ _*:_ _-:>_ : (X -> Set) -> (X -> Set) -> (X -> Set)
  (S +: T) x = S x + T x
  (S *: T) x = S x * T x
  (S -:> T) x = S x -> T x

  [_] <_> : (X -> Set) -> Set
  [ P ] = forall {x} -> P x
  < P > = X >< P
  infix 5 [_] <_>
  infixr 10 _-:>_
  infixr 20 _+:_
  infixr 30 _*:_

data _~_ {X : Set}(x : X) : X -> Set where
  r~ : x ~ x
{-# BUILTIN EQUALITY _~_ #-}


_>!<_ : (S : Set)(T : S -> Set) -> Set
S >!< T = S >< \ s -> T s * ((x : S) -> T x -> x ~ s)


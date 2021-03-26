module Jaco where

data Poly (I : Set) : Set1 where
  va : I -> Poly I
  sg : (A : Set) -> (A -> Poly I) -> Poly I
  _**_ : Poly I -> Poly I -> Poly I
  ko : Set -> Poly I

record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_ public
infixr 4 _,_
_*_ : Set -> Set -> Set
S * T = S >< \ _ -> T

data Zero : Set where
record One : Set where constructor <>
data Two : Set where ff tt : Two

_+_ : Set -> Set -> Set
S + T = Two >< \ { ff -> S ; tt -> T }

_++_ : forall {I} -> Poly I -> Poly I -> Poly I
P ++ Q = sg Two \ { ff -> P ; tt -> Q }

data _~_ {X : Set}(x : X) : X -> Set where
  r~ : x ~ x

[_]P : forall {I} -> Poly I -> (I -> Set) -> Set
[ va i ]P   X = X i
[ sg A B ]P X = A >< \ a -> [ B a ]P X
[ P ** Q ]P X = [ P ]P X * [ Q ]P X
[ ko A ]P   X = A

Grad : forall {I} -> Poly I -> I -> Poly I
Grad (va j)   i = ko (j ~ i)
Grad (sg A B) i = sg A \ a -> Grad (B a) i
Grad (P ** Q) i = (Grad P i ** Q) ++ (P ** Grad Q i)
Grad (ko A)   i = ko Zero

Div : forall {I} -> Poly I -> (I -> Set) -> Set
Div {I} P X = I >< \ i -> [ Grad P i ]P X * X i

up : forall {I}{X : I -> Set}(P : Poly I) -> Div P X -> [ P ]P X
up (va i)   (_ , r~            , x) = x
up (sg A B) (_ , (a , b')      , x) = a , up (B a) (_ , b' , x)
up (P ** Q) (_ , (ff , p' , q) , x) = up P (_ , p' , x) , q
up (P ** Q) (_ , (tt , p , q') , x) = p , up Q (_ , q' , x)

leftest : forall {I}{X : I -> Set}(P : Poly I) ->
  [ P ]P X -> Div P X + [ P ]P \ _ -> Zero
leftest (va i) x = ff , i , r~ , x
leftest (sg A B) (a , b) with leftest (B a) b
... | ff , i , b' , x = ff , i , (a , b') , x
... | tt , b0 = tt , a , b0
leftest (P ** Q) (p , q) with leftest P p
... | ff , i , p' , x = ff , i , (ff , p' , q) , x
... | tt , p0 with leftest Q q
... | ff , i , q' , x = ff , i , (tt , p , q') , x
... | tt , q0 = tt , p0 , q0
leftest (ko A) a = tt , a

righter : forall {I}{X : I -> Set}(P : Poly I) ->
  Div P X ->
  Div P X + [ P ]P X
righter (va i) (_ , r~ , x) = tt , x
righter (sg A B) (_ , (a , b') , x) with righter (B a) (_ , b' , x)
... | ff , j , c' , y = ff , j , (a , c') , y
... | tt , r = tt , a , r
righter (P ** Q) (_ , (ff , p' , q) , x) with righter P (_ , p' , x)
... | ff , j , r' , y = ff , j , (ff , r' , q) , y
... | tt , p with leftest Q q
... | ff , j , q' , y = ff , j , (tt , p , q') , y
... | tt , _ = tt , p , q
righter (P ** Q) (_ , (tt , p , q') , x) with righter Q (_ , q' , x)
... | ff , j , r' , y = ff , j , (tt , p , r') , y
... | tt , q = tt , p , q

J : forall {O I} ->
    (O -> Poly I) -> (I * O -> Poly I)
J F (i , o) = Grad (F o) i

data Mu (I : Set)(F : I -> Poly I)(i : I) : Set
  where <_> : [ F i ]P (Mu I F) -> Mu I F i

data Star {X : Set}(R : X -> X -> Set)(x : X) : X -> Set where
  [] : Star R x x
  _,-_ : forall {y z} -> R x y -> Star R y z -> Star R x z

Zipper : (I : Set)(F : I -> Poly I)(hole root : I) -> Set
Zipper I F = Star \ i o -> [ J F (i , o) ]P (Mu I F)

top : forall {I}{F : I -> Poly I}{hole root : I} ->
  Mu I F hole -> Zipper I F hole root -> Mu I F root
top t [] = t
top {F = F} t (_,-_ {y = o} f' f's) = top < up (F o) (_ , f' , t) > f's

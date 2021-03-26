module Jaco where

-- Polynomials in some set I variables

data Poly (I : Set) : Set1 where
  va    : I -> Poly I                           -- variable
  _>P<_ : (A : Set) -> (A -> Poly I) -> Poly I  -- dependent pair with a tag
  _*P_  : Poly I -> Poly I -> Poly I            -- pair of polynomials
  ko    : Set -> Poly I                         -- constant

-- To interpret polynomials, we need some basic kit.

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

_+P_ : forall {I} -> Poly I -> Poly I -> Poly I
P +P Q = Two >P< \ { ff -> P ; tt -> Q }


-- semantics of Polynomials

[_]P : forall {I} -> Poly I -> (I -> Set) -> Set
[ va i ]P    X = X i
[ A >P< B ]P X = A >< \ a -> [ B a ]P X
[ P *P Q ]P  X = [ P ]P X * [ Q ]P X
[ ko A ]P    X = A


-- Equality

data _~_ {X : Set}(x : X) : X -> Set where
  r~ : x ~ x


-- Liftings to indexed sets

[_] : {I : Set} -> (I -> Set) -> Set  -- necessity
[ P ] = forall {i} -> P i

<_> : {I : Set} -> (I -> Set) -> Set  -- possibility
< P > = _ >< P

_+:_ _*:_ _-:>_ : {I : Set} -> (I -> Set) -> (I -> Set) -> I -> Set
(P +: Q) i = P i + Q i
(P *: Q) i = P i * Q i
(P -:> Q) i = P i -> Q i

True : forall {I : Set} -> I -> Set
True _ = One


-- partial derivatives of polynomials

parD : forall {I} -> I -> Poly I -> Poly I
parD i (va j)   = ko (j ~ i)
parD i (A >P< B) = A >P< \ a -> parD i (B a)
parD i (P *P Q) = (parD i P *P Q) +P (P *P parD i Q)
parD i (ko A)   = ko Zero


-- "gradient vector" collects all the partial derivatives

Grad : forall {I} -> (I -> Set) -> Poly I -> I -> Set
Grad X P i = [ parD i P ]P X

-- "divergence" collects all the ways to be visited

Div : forall {I} -> (I -> Set) -> Poly I -> Set
Div {I} X P = < Grad X P *: X >

-- we can always stop visiting

up : forall {I}{X : I -> Set}(P : Poly I) -> Div X P -> [ P ]P X
up (va i)   (_ , r~            , x) = x
up (A >P< B) (_ , (a , b')      , x) = a , up (B a) (_ , b' , x)
up (P *P Q) (_ , (ff , p' , q) , x) = up P (_ , p' , x) , q
up (P *P Q) (_ , (tt , p , q') , x) = p , up Q (_ , q' , x)

-- we can find the leftmost child or discover we are childless

leftest : forall {I}{X : I -> Set}(P : Poly I) ->
  [ P ]P X -> Div X P + [ P ]P \ _ -> Zero
leftest (va i) x = ff , i , r~ , x
leftest (A >P< B) (a , b) with leftest (B a) b
... | ff , i , b' , x = ff , i , (a , b') , x
... | tt , b0 = tt , a , b0
leftest (P *P Q) (p , q) with leftest P p
... | ff , i , p' , x = ff , i , (ff , p' , q) , x
... | tt , p0 with leftest Q q
... | ff , i , q' , x = ff , i , (tt , p , q') , x
... | tt , q0 = tt , p0 , q0
leftest (ko A) a = tt , a

-- we can try to move right and move up if there's nowhere to move to

righter : forall {I}{X : I -> Set}(P : Poly I) ->
  Div X P ->
  Div X P + [ P ]P X
righter (va i) (_ , r~ , x) = tt , x
righter (A >P< B) (_ , (a , b') , x) with righter (B a) (_ , b' , x)
... | ff , j , c' , y = ff , j , (a , c') , y
... | tt , r = tt , a , r
righter (P *P Q) (_ , (ff , p' , q) , x) with righter P (_ , p' , x)
... | ff , j , r' , y = ff , j , (ff , r' , q) , y
... | tt , p with leftest Q q
... | ff , j , q' , y = ff , j , (tt , p , q') , y
... | tt , _ = tt , p , q
righter (P *P Q) (_ , (tt , p , q') , x) with righter Q (_ , q' , x)
... | ff , j , r' , y = ff , j , (tt , p , r') , y
... | tt , q = tt , p , q


-- now, the general situation is that we have a *family* of polynomials
-- which has a Jacobian matrix, indexed the sort of the hole and the sort
-- of the node it sits inside

Jaco : forall {O I} ->
    (O -> Poly I) -> (I * O -> Poly I)
Jaco F (i , o) = parD i (F o)

-- tie the knot and obtain the generic polynomial datatype

data Mu {I : Set}(F : I -> Poly I)(i : I) : Set
  where con : [ F i ]P (Mu F) -> Mu F i

-- sequences of steps

data Star {X : Set}(R : X -> X -> Set)(x : X) : X -> Set where
  [] : Star R x x
  _,-_ : forall {y z} -> R x y -> Star R y z -> Star R x z

-- a one-hole context is a sequence of steps from hole to root where
-- each step is given by the Jacobian of the family of polynomials which
-- generates the datatype

_>[_]>_ : {I : Set}(hole : I)(F : I -> Poly I)(root : I) -> Set
hole >[ F ]> root = Star (\ i o -> [ Jaco F (i , o) ]P (Mu F)) hole root

-- a zipper is, for some sort, a term of that sort and a context from that
-- sort back to the root

Zipper : forall {I}(F : I -> Poly I)(root : I) -> Set
Zipper F root = < Mu F *: (_>[ F ]> root) >

-- we can zoom all the way out

top : forall {I}{F : I -> Poly I} -> [ Zipper F -:> Mu F ]
top {I}{F}{root} (_ , t , z) = go t z where
  go : forall {hole} -> Mu F hole -> hole >[ F ]> root -> Mu F root
  go t [] = t
  go t (_,-_ {y = o} f' f's) = go (con (up (F o) (_ , f' , t))) f's

-- we can try to visit our left child

leftChild : forall {I}{F : I -> Poly I} -> [ Zipper F -:> (True +: Zipper F) ]
leftChild {I}{F} (o , con ts , z) with leftest (F o) ts
... | ff , _ , c , t = tt , _ , t , (c ,- z)
... | tt , _ = ff , <>

-- we can try to move right

rightSib : forall {I}{F : I -> Poly I} -> [ Zipper F -:> (True +: Zipper F) ]
rightSib {I} {F} (o , t , []) = ff , <>
rightSib {I} {F} (_ , t , (_,-_ {y = o} c z)) with righter (F o) (_ , c , t)
... | ff , _ , d , u = tt , _ , u , (d ,- z)
... | tt , _ = ff , <>

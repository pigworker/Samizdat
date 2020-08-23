module Cats where

data _~_ {X : Set}(x : X) : X -> Set where
  r~ : x ~ x

record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_ public
infixr 4 _,_

_*_ : Set -> Set -> Set
S * T = S >< \ _ -> T

_:*_ : {X : Set} ->
  (X -> Set) -> (X -> Set) -> (X -> Set)
(P :* Q) x = P x * Q x

record <_> {X : Set}(P : X -> Set) : Set where
  constructor !_
  field
    {wit} : X
    prf  : P wit
open <_> public
infixr 4 !_

data Nat : Set where
  ze : Nat
  su : Nat -> Nat

data [_+N_]~_ : Nat -> Nat -> Nat -> Set where
  ze : forall {y}
       -> [ ze +N y ]~ y
  su : forall {x y z}
       -> [ x +N y ]~ z
       -> [ su x +N y ]~ su z
  
mk+N : forall x y -> < [ x +N y ]~_ >
mk+N ze     y = ! ze
mk+N (su x) y with ! p <- mk+N x y = ! su p

unique+N : forall {x y}(a b : < [ x +N y ]~_ >) -> a ~ b
unique+N (! ze) (! ze) = r~
unique+N (! su a) (! su b)
  with r~ <- unique+N (! a) (! b) = r~

_+N_ : Nat -> Nat -> Nat
x +N y = wit (mk+N x y)

asso+N : forall {i j k l}
  -> < ([ i +N j ]~_) :* ([_+N k ]~ l) >
  -> < ([ j +N k ]~_) :* ([ i +N_]~ l) >

asso+N (! ze   , b)    = ! b , ze
asso+N (! su a , su b)
  with ! c , d <- asso+N (! a , b)
  = ! c , su d
  
data Vec (X : Set) : Nat -> Set where
  [] : Vec X ze
  _,-_ : forall {n} -> X -> Vec X n -> Vec X (su n)

data [_+V_]~_ {X : Set} : forall {i j k} ->
  Vec X i -> Vec X j -> Vec X k -> Set
  where
  ze : forall {j}{ys : Vec X j} -> [ [] +V ys ]~ ys
  su : forall {i j k x}
       {xs : Vec X i}{ys : Vec X j}{zs : Vec X k}
       -> [ xs +V ys ]~ zs
       -> [ (x ,- xs) +V ys ]~ (x ,- zs)

mk+V : forall {X i j}(xs : Vec X i)(ys : Vec X j) ->
  <(\ k -> <_> {Vec X k} ([ xs +V ys ]~_))>
mk+V [] ys = ! ! ze
mk+V (x ,- xs) ys with ! ! p <- mk+V xs ys = ! ! su p

lem+VN : forall {X i j k}
  {xs : Vec X i}{ys : Vec X j}{zs : Vec X k}
  -> [ xs +V ys ]~ zs
  -> [ i +N j ]~ k
lem+VN ze = ze
lem+VN (su p) = su (lem+VN p)

asso+V : forall {X}{i j k l}
  {ws : Vec X i}{xs : Vec X j}{ys : Vec X k}{zs : Vec X l}
  -> <(\ m -> <_> {Vec X m}
       (([ ws +V xs ]~_) :* ([_+V ys ]~ zs)))>
  -> <(\ m -> <_> {Vec X m}
       (([ xs +V ys ]~_) :* ([ ws +V_]~ zs)))>
asso+V (! ! (ze , q)) = ! ! q , ze
asso+V (! ! (su p , su q))
  with ! ! r , s <- asso+V (! ! p , q)
  = ! ! r , su s

_+V_ : forall {X i j}
  -> Vec X i -> Vec X j -> Vec X (i +N j)
_+V_ {X}{i}{j} xs ys
  with p <- mk+N i j | ! q <- mk+V xs ys
     | p' <- lem+VN (prf q)
     | r~ <- unique+N p (! p')
  = wit q

{-# OPTIONS --prop #-}

module VecApart where

data Ff : Prop where
record Zero : Set where
  constructor bad
  field
    dab : Ff
record One : Set where constructor <>
data Two : Set where ff tt : Two
record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
infixr 30 _,_
open _><_ public
_*_ : Set -> Set -> Set
S * T = S >< \ _ -> T
_+_ : Set -> Set -> Set
S + T = Two >< \ { ff -> S ; tt -> T }
infixr 20 _><_ _*_
infixr 10 _+_
la_ : forall {l S T}{P : S >< T -> Set l}
  -> ((s : S) -> (t : T s) -> P (s , t))
  -> (x : S >< T) -> P x
la_ f (s , t) = f s t
infixr 0 la_

_<?>_ : forall {l}{P : Two -> Set l}
     -> P ff -> P tt -> (b : Two) -> P b
(pf <?> pt) ff = pf
(pf <?> pt) tt = pt

ko_ : forall {k l}{X : Set k}{Y : X -> Set l} -> (x : X)(y : Y x) -> X
(ko x) y = x

module _ {X : Set} where
  _*:_ _+:_ _-:>_ : (X -> Set) -> (X -> Set) -> (X -> Set)
  infixr 20 _*:_
  (P *: Q) x = P x * Q x
  infixr 10 _+:_
  (P +: Q) x = P x + Q x
  infixr 0 _-:>_
  (P -:> Q) x = P x -> Q x
  
  <_> [_] : (X -> Set) -> Set
  < P > = X >< P
  [ P ] = forall {x} -> P x

_$>_ : forall {i j k}
       {A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k}
       (f : (a : A) -> B a)
       (g : {a : A}(b : B a) -> C a b)
       (a : A) -> C a (f a)
(f $> g) a = g (f a)

data Nat : Set where
  ze : Nat
  su : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

data Vec {l}(X : Set l) : Nat -> Set l where
  []   : Vec X 0
  _,-_ : {n : Nat}(x : X)(xs : Vec X n) -> Vec X (su n)

infixr 50 _,-_

pure : forall {l}{X : Set l}{n} -> X -> Vec X n
pure {n = ze} x = []
pure {n = su n} x = x ,- pure x

infixl 60 _<*>_
_<*>_ : forall {k l}{S : Set k}{T : Set l}{n}
     -> Vec (S -> T) n -> Vec S n -> Vec T n
[] <*> [] = []
(f ,- fs) <*> (s ,- ss) = f s ,- fs <*> ss

module _ {X : Set} where

  infix 40 _<=_
  data _<=_ : {n m : Nat}(xs : Vec X n)(ys : Vec X m) -> Set where
    _^-_ : forall {n m : Nat}{xs : Vec X n} y {ys : Vec X m}
        ->      xs <=      ys
        ->      xs <= y ,- ys
    _,-_ : forall {n m : Nat} x {xs : Vec X n}{ys : Vec X m}
        ->      xs <=      ys
        -> x ,- xs <= x ,- ys
    []   : [] <= []
  infixr 50 _^-_

  io : forall {n}{xs : Vec X n} -> xs <= xs
  io {xs = []} = []
  io {xs = x ,- xs} = x ,- io

  infixr 50 _&-_
  _&-_ : forall {n m l}{xs : Vec X n}{ys : Vec X m}{zs : Vec X l}
      -> xs <= ys -> ys <= zs -> xs <= zs
  th &- (y ^- ph) = y ^- th &- ph
  (.x ^- th) &- (x ,- ph) = x ^- th &- ph
  (.x ,- th) &- (x ,- ph) = x ,- th &- ph
  [] &- [] = []

  no : forall {n}{xs : Vec X n} -> [] <= xs
  no {xs = []} = []
  no {xs = x ,- xs} = x ^- no

  infix 30 _<-_
  _<-_ : forall (x : X){n}(xs : Vec X n) -> Set
  x <- xs = x ,- [] <= xs

  infix 30 #_
  #_ : {n : Nat}(xs : Vec X n) -> Set
  # xs = forall x -> x ,- x ,- [] <= xs -> Zero

  #0 : # []
  #0 _ ()

  #1 : {x : X} -> # x ,- []
  #1 _ (y ^- ())
  #1 _ (x ,- ())

  infixr 30 _?#_
  _?#_ : forall {n m}{xs : Vec X n}{ys : Vec X m}
      -> xs <= ys -> # ys -> # xs
  (th ?# d) x ph = d x (ph &- th)

_-_ : (X : Set){n : Nat} -> Vec X n -> Set
X - xs = X >< \ x -> # x ,- xs

module _ {l}{X : Set l} where

  data _~_ (x : X) : X -> Set l where
    r~ : x ~ x
    
  subst : forall {k x y} -> x ~ y -> (P : X -> Set k) -> P x -> P y
  subst r~ P p = p

  _~[_>_ : forall x {y z} -> x ~ y -> y ~ z -> x ~ z
  x ~[ r~ > q = q
  _<_]~_ : forall x {y z} -> y ~ x -> y ~ z -> x ~ z
  x < r~ ]~ q = q
  infixr 3 _~[_>_ _<_]~_
  _[QED] : forall x -> x ~ x
  x [QED] = r~
  infix 4 _[QED]

  !~_ : forall x -> x ~ x
  !~ x = r~
  infixl 6 !~_

  _~/~_ : X -> X -> Set l
  x ~/~ y = x ~ y -> Zero

{-# BUILTIN EQUALITY _~_ #-}

_~$~_ : forall {k l}{S : Set k}{T : Set l}{f g : S -> T}{x y : S}
     -> f ~ g -> x ~ y -> f x ~ g y
r~ ~$~ r~ = r~
infixl 5 _~$~_

infix 0 _<=>_
record _<=>_ (S T : Set) : Set where
  field
    l2r : S -> T
    r2l : T -> S
    l2r2l : (s : S) -> r2l (l2r s) ~ s
    r2l2r : (t : T) -> l2r (r2l t) ~ t
open _<=>_ public

module _ {X : Set} where

  diffDist : {x y : X} -> x ~/~ y -> # x ,- y ,- []
  diffDist nq x (_ ^- _ ^- ())
  diffDist nq x (_ ^- (.x ,- ()))
  diffDist nq x (.x ,- (.x ,- th)) = nq r~
  
  distDiff : {x y : X} -> # x ,- y ,- [] -> x ~/~ y
  distDiff di r~ = di _ io

  no~ : forall {n}{xs : Vec X n}(th ph : [] <= xs) -> th ~ ph
  no~ (y ^- th) (.y ^- ph) = !~ y ^-_ ~$~ no~ th ph
  no~ [] [] = r~

  atMost1 : forall {n}{xs : Vec X n}(p : # xs){x}(i j : x <- xs) -> i ~ j
  atMost1 p (y ^- i) (.y ^- j) = !~ y ^-_ ~$~ atMost1 (y ^- io ?# p) i j
  atMost1 p (y ^- i) (.y ,- j) with () <- p y (y ,- i)
  atMost1 p (x ,- i) (.x ^- j) with () <- p x (x ,- j)
  atMost1 p (x ,- i) (.x ,- j) = !~ x ,-_ ~$~ no~ i j

  twoDiff : forall {n}{xs : Vec X n}{y z : X}
         -> # y ,- xs -> # z ,- xs -> y ~/~ z -> # y ,- z ,- xs
  twoDiff yd zd ynz x (y ^- z ^- th) = yd x (y ^- th)
  twoDiff yd zd ynz x (y ^- (.x ,- th)) = zd x (x ,- th)
  twoDiff yd zd ynz x (.x ,- (y ^- th)) = yd x (x ,- th)
  twoDiff yd zd ynz x (.x ,- (.x ,- th)) = ynz r~

Dec : Set -> Set
Dec X = (X -> Zero) + X

DecEq : Set -> Set
DecEq X = (x y : X) -> Dec (x ~ y)

record Datoid : Set1 where
  constructor _/~?_
  field
    Data : Set
    _~?_ : (x y : Data) -> Dec (x ~ y)

module _ (D : Datoid) where
  module Private where
    X = Datoid.Data D
    _~?_ = Datoid._~?_ D
  open Private

  dec- : forall {n}{xs : Vec X n} -> DecEq (X - xs)
  dec- (x , p) (y , q) with x ~? y
  dec- (x , p) (y , q)  | ff , nq = ff , \ { r~ -> nq r~ }
  dec- (x , p) (.x , q) | tt , r~ = tt , r~

  seek : forall {n}(xs : Vec X n) -> # xs ->
         (x : X) -> # x ,- xs + x <- xs
  seek [] xd x = ff , #1
  seek (y ,- xs) xd x with x ~? y
  seek (y ,- xs) xd x | ff , p with seek xs (y ^- io ?# xd) x
  seek (y ,- xs) yd x | ff , p | ff , xd = ff , twoDiff xd yd p
  seek (y ,- xs) xd x | ff , p | tt , i  = tt , y ^- i
  seek (y ,- xs) xd .y | tt , r~ = tt , y ,- no

  module _ {n : Nat}(xs : Vec X n)(xd : # xs) where

    dIso : X <=> (X - xs) + < _<- xs >
    l2r dIso x with seek xs xd x
    l2r dIso x | ff , w = ff , x , w
    l2r dIso x | tt , w = tt , x , w
    r2l dIso (ff , x , w) = x
    r2l dIso (tt , x , w) = x
    l2r2l dIso x with seek xs xd x
    l2r2l dIso x | ff , w = r~
    l2r2l dIso x | tt , w = r~
    r2l2r dIso (ff , x , w) with seek xs xd x
    r2l2r dIso (ff , x , w) | ff , v = r~
    r2l2r dIso (ff , x , w) | tt , v with () <- w x (x ,- v)
    r2l2r dIso (tt , x , w) with seek xs xd x
    r2l2r dIso (tt , x , w) | ff , v with () <- v x (x ,- w)
    r2l2r dIso (tt , x , w) | tt , v = !~ tt ,_ ~$~ (!~ x ,_ ~$~ atMost1 xd v w)

  module _ {n : Nat}(x : X)(xs : Vec X n)(xxd : # x ,- xs) where

    hIso : X - xs <=> X - x ,- xs + < _~ x > 
    l2r hIso (y , p) with y ~? x
    l2r hIso (y , p) | ff , n = ff , y , twoDiff p xxd n
    l2r hIso (y , p) | tt , q = tt , y , q
    r2l hIso (ff , y , p) = y , y ,- x ^- io ?# p
    r2l hIso (tt , .x , r~) = x , xxd
    l2r2l hIso (y , p) with y ~? x
    l2r2l hIso (y , p) | ff , q = r~
    l2r2l hIso (y , p) | tt , r~ = r~
    r2l2r hIso (ff , y , p) with y ~? x
    r2l2r hIso (ff , y , p) | ff , q = r~
    r2l2r hIso (ff , y , p) | tt , r~ with () <- p x (x ,- x ,- no)
    r2l2r hIso (tt , y , r~) with x ~? x
    r2l2r hIso (tt , y , r~) | ff , q with () <- q r~
    r2l2r hIso (tt , y , r~) | tt , r~ = r~

open Datoid

record Con : Set1 where
  constructor _<|_
  field
    Sh : Set
    Po : Sh -> Datoid
open Con public

record Der (n : Nat)(C : Con)(X : Set) : Set where
  constructor _<_^_!_
  field
    shape : Sh C
    holes : Vec (Data (Po C shape)) n
    apart : # holes
    stuff : Data (Po C shape) - holes -> X

plug : forall {n C X} -> Der (su n) C X -> X -> Der n C X
plug {C = S <| P} (s < h ,- hs ^ hd ! f) x =
  let Ps /~? eq? = P s in
  s < hs ^ h ^- io ?# hd ! (l2r (hIso (P s) h hs hd) $> (la f <?> (ko x)))

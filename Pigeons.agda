module Pigeons where


------------------------------------------------------------------------------
-- TOTALLY STANDARD PRELIMINARIES
------------------------------------------------------------------------------

data _~_ {X : Set}(x : X) : X -> Set where
  r~ : x ~ x

data Zero : Set where

data Nat : Set where
  su : Nat -> Nat
  ze : Nat

record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_ public
_*_ : Set -> Set -> Set
S * T = S >< \ _ -> T
infixr 20 _*_ _,_


------------------------------------------------------------------------------
-- IDIOSYNCRATIC PRELIMINARIES re THINNINGS
------------------------------------------------------------------------------

data _c=_ : Nat -> Nat -> Set where
  no : forall {n m} -> n c= m ->    n c= su m
  su : forall {n m} -> n c= m -> su n c= su m
  ze :                           ze   c= ze

none : forall {n} -> ze c= n
none {su n} = no none
none {ze} = ze

-- relational diagrammatic composition
data [_-<_]~_ : forall {l n m}
    ->  l c= n  ->  n c= m  ->  l c= m  -> Set where
  no : forall {l n m}{th : l c= n}{ph : n c= m}{ps : l c= m}
    -> [    th -<    ph ]~    ps
    -> [    th -< no ph ]~ no ps
  nosu : forall {l n m}{th : l c= n}{ph : n c= m}{ps : l c= m}
    -> [    th -<    ph ]~    ps
    -> [ no th -< su ph ]~ no ps
  su : forall {l n m}{th : l c= n}{ph : n c= m}{ps : l c= m}
    -> [    th -<    ph ]~    ps
    -> [ su th -< su ph ]~ su ps
  ze : [ ze    -< ze    ]~ ze

nonethnone : forall {i j}{th : i c= j} -> [ none -< th ]~ none
nonethnone {th = no th} = no nonethnone
nonethnone {th = su th} = nosu nonethnone
nonethnone {th = ze}    = ze

-- candidate pullback
record Common {i j n} h (th : i c= n)(ph : j c= n) : Set where
  constructor common
  field
    {leftInc}   : h c= i
    {midInc}    : h c= n
    {rightInc}  : h c= j
    leftTri     : [ leftInc  -< th ]~ midInc
    rightTri    : [ rightInc -< ph ]~ midInc


------------------------------------------------------------------------------
-- IDIOSYNCRATIC PRELIMINARIES re ADDITION
------------------------------------------------------------------------------

-- relational addition
data [_+_]~_ : Nat -> Nat -> Nat -> Set where
  su : forall {l n m}
    -> [    l + n ]~    m
    -> [ su l + n ]~ su m
  ze : (m : Nat)
    -> [ ze   + m ]~    m

su' : forall {l n m} -> [ l + n ]~ m -> [ l + su n ]~ su m
su' (su c) = su (su' c)
su' (ze n) = ze (su n)

rightSu : forall {l n m}
     -> [ l + su n ]~ m
     -> _ >< \ p -> (m ~ su p) * [ l + n ]~ p
rightSu (su c) with _ , r~ , u <- rightSu c = _ , r~ , su u
rightSu (ze .(su _)) = _ , r~ , ze _


------------------------------------------------------------------------------
-- THE PIGEONHOLE PRINCIPLE
------------------------------------------------------------------------------

pigeons : forall {i j n k m}
       -> (th : i c= n)
       -> (ph : j c= n)
       -> [    i + j ]~ m
       -> [ su n + k ]~ m
       -> Common (su ze) th ph
pigeons (no th) (no ph) ij (su (su nk))
  with common u v <- pigeons th ph ij (su (su' nk))
     = common (no u) (no v)
pigeons (no th) (su ph) ij (su nk)
  with _ , r~ , d <- rightSu ij
  with common u v <- pigeons th ph d nk
     = common (no u) (nosu v)
pigeons (su th) (no ph) (su ij) (su nk)
  with common u v <- pigeons th ph ij nk
     = common (nosu u) (no v)
pigeons (su th) (su ph) ij nk
     = common (su nonethnone) (su nonethnone)
pigeons ze ze (ze .ze) ()

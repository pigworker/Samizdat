module Nellist where

-- see you B, raise you S
_-_ : forall {i j k}
      {A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k}
      (f : (a : A) -> B a)
      (g : {a : A}(b : B a) -> C a b)
      (a : A) -> C a (f a)
(f - g) a = g (f a)

infixl 10 _-_

data _~_ {X : Set}(x : X) : X -> Set where
  r~ : x ~ x
{-# BUILTIN EQUALITY _~_ #-}

_[_>_ : forall {X} x {y z : X} -> x ~ y -> y ~ z -> x ~ z
x [ r~ > q = q
_<_]_ : forall {X} x {y z : X} -> y ~ x -> y ~ z -> x ~ z
x < r~ ] q = q
infixr 4 _[_>_ _<_]_
_[QED] : forall {X}(x : X) -> x ~ x
x [QED] = r~
infixr 5 _[QED]

_$~_ : forall {X Y}(f : X -> Y){x x' : X} -> x ~ x' -> f x ~ f x'
f $~ r~ = r~
resp2 : forall {X Y Z}(f : X -> Y -> Z){x x' : X} -> x ~ x' -> {y y' : Y} -> y ~ y' -> f x y ~ f x' y'
resp2 f r~ r~ = r~

record Nellist (X : Set) : Set
data Neltail (X : Set) : Set

record Nellist X where
  inductive
  constructor _,_
  field
    head : X
    tail : Neltail X
infixr 10 _,_
open Nellist

data Neltail X where
  [] : Neltail X
  !_ : Nellist X -> Neltail X
infixr 10 !_

_++_ : forall {X} -> Nellist X -> Neltail X -> Nellist X
_++'_ : forall {X} -> Neltail X -> Neltail X -> Neltail X
(x , xs) ++ ys = x , (xs ++' ys)
[] ++' ys = ys
(! xs) ++' ys = ! (xs ++ ys)

map : forall {X Y} -> (X -> Y) -> Nellist X -> Nellist Y
mapt : forall {X Y} -> (X -> Y) -> Neltail X -> Neltail Y
map f (x , xs) = f x , mapt f xs
mapt f [] = []
mapt f (! xs) = ! map f xs

mapnelcat : forall {X Y}(f : X -> Y) xs ys ->
  map f (xs ++ ys) ~ (map f xs ++ mapt f ys)
mapnelcat' : forall {X Y}(f : X -> Y) xs ys ->
  mapt f (xs ++' ys) ~ (mapt f xs ++' mapt f ys)
mapnelcat f (x , xs) ys rewrite mapnelcat' f xs ys = r~
mapnelcat' f [] ys = r~
mapnelcat' f (! xs) ys rewrite mapnelcat f xs ys = r~

mapmap : forall {X Y Z}(f : X -> Y)(g : Y -> Z)(h : X -> Z)
  (q : (x : X) -> g (f x) ~ h x)
  (xs : Nellist X) ->
  map g (map f xs) ~ map h xs
maptmapt : forall {X Y Z}(f : X -> Y)(g : Y -> Z)(h : X -> Z)
  (q : (x : X) -> g (f x) ~ h x)
  (xs : Neltail X) ->
  mapt g (mapt f xs) ~ mapt h xs
mapmap f g h q (x , xs) rewrite q x | maptmapt f g h q xs = r~
maptmapt f g h q [] = r~
maptmapt f g h q (! xs) rewrite mapmap f g h q xs = r~

decorot : forall {X} -> Neltail X -> Neltail X -> Neltail (Nellist X)
decorot' : forall {X} -> Nellist X -> Neltail X -> Neltail (Nellist X)
decorot [] ys = []
decorot (! xs) ys = ! (xs ++ ys) , decorot' xs ys
decorot' (x , xs) ys = decorot xs (ys ++' (! x , []))

catnil : forall {X}(xs : Neltail X) -> (xs ++' []) ~ xs
catnil [] = r~
catnil (! x , xs) = !_ $~ ((x ,_) $~ catnil xs)

catasso : forall {X}(xs ys zs : Neltail X) -> ((xs ++' ys) ++' zs) ~ (xs ++' (ys ++' zs))
catasso [] ys zs = r~
catasso (! x , xs) ys zs = !_ $~ ((x ,_) $~ catasso xs ys zs)

lemma : forall {X}(xs ys zs : Neltail X) ->
  decorot (xs ++' ys) zs ~
  (decorot xs (ys ++' zs) ++' decorot ys (zs ++' xs))
lemma [] ys zs = decorot ys $~ (zs < catnil zs ] zs ++' [] [QED])
lemma (! x , xs) ys zs = !_ $~ resp2 _,_
  ((x ,_) $~ catasso xs ys zs)
  (decorot (xs ++' ys) (zs ++' (! x , [])) [ lemma xs ys (zs ++' (! x , [])) >
   (decorot xs (ys ++' (zs ++' (! x , []))) ++'
    decorot ys ((zs ++' (! x , [])) ++' xs))
    [ resp2 _++'_
      (decorot xs $~ ((ys ++' (zs ++' (! x , [])))
                     < catasso ys zs (! x , []) ]
                     ((ys ++' zs) ++' (! x , [])) [QED]))
      (decorot ys $~ (((zs ++' (! x , [])) ++' xs)
                     [ catasso zs (! x , []) xs >
                     (zs ++' (! x , xs)) [QED])) >
   (decorot xs ((ys ++' zs) ++' (! x , [])) ++'
   decorot ys (zs ++' (! x , xs))) [QED])

deco : forall {X} -> Nellist X -> Nellist (Nellist X)
deco xs = xs , decorot (tail xs) (! head xs , [])

here : forall {X} -> Nellist X -> X
here = head

data Nat : Set where
  ze : Nat
  su : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

test = deco (1 , ! 2 , ! 3 , ! 4 , [])

check : deco test ~ map deco test
check = r~

law1 : forall {X}(xs : Nellist X) -> here (deco xs) ~ xs
law1 (x , xs) = r~

law2 : forall {X}(xs : Nellist X) -> map here (deco xs) ~ xs
law2' : forall {X} xs ys -> mapt (head{X}) (decorot xs ys) ~ xs
law2 (x , xs) = (x ,_) $~ law2' xs (! x , [])
law2' [] ys = r~
law2' (! x , xs) ys = !_ $~ ((x ,_) $~ law2' xs _)

law3 : forall {X}(xs : Nellist X) ->
  deco (deco xs) ~ map deco (deco xs)
law3' : forall {X}(xs ys : Neltail X) ->
  decorot (decorot xs ys) (decorot ys xs) ~
  mapt deco (decorot xs ys)
law3 (x , xs) = (((x , xs) , decorot xs (! x , [])) ,_) $~ law3' xs (! x , [])
law3' [] ys = r~
law3' (! x , xs) ys = !_ $~ resp2 _,_
  (((x , (xs ++' ys)) ,_) $~ (
    (decorot xs (ys ++' (! x , [])) ++' decorot ys (! x , xs)) < lemma xs ys (! x , []) ]
     decorot (xs ++' ys) (! x , []) [QED]))
  (decorot (decorot xs (ys ++' (! x , [])))
      (decorot ys (! x , xs) ++' (! (x , (xs ++' ys)) , []))
     [ decorot (decorot xs (ys ++' (! x , []))) $~
       ((decorot ys (! x , xs) ++' (! (x , (xs ++' ys)) , []))
         < lemma ys (! x , []) xs ]
        decorot (ys ++' (! x , [])) xs [QED])
     >
   decorot (decorot xs (ys ++' (! x , []))) (decorot (ys ++' (! x , [])) xs)
     [ law3' xs (ys ++' (! x , []))>
   mapt deco (decorot xs (ys ++' (! x , []))) [QED])

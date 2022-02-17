module FamPowSet where

------------------------------------------------------
-- diagrammatic composition; would prefer semicolon --
------------------------------------------------------
_%_ : forall {i j k}{R : Set i}{S : Set j}{T : Set k}
  -> (R -> S) -> (S -> T) -> R -> T
(f % g) x = g (f x)

------------------------------------------
-- overly intensional equality, but hey --
------------------------------------------
data _~_ {X : Set}(x : X) : X -> Set where
  r~ : x ~ x
{-# BUILTIN EQUALITY _~_ #-}

sym : forall {X : Set}{x y : X} -> x ~ y -> y ~ x
sym r~ = r~

refl : forall {X}(x : X) -> x ~ x
refl _ = r~

_~$~_ : forall {X Y}{f g : X -> Y}{a b : X} -> f ~ g -> a ~ b -> f a ~ g b
r~ ~$~ r~ = r~

--------------------------------
-- dependent pairs made infix --
--------------------------------
record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_ public

---------------------------------
-- What is (small) Fam? ---------
---------------------------------
{-
Fam is the covariant proof-relevant power set functor.
Fam X picks a subset of X as the image of a function.
-}
record Fam (X : Set) : Set1 where
  constructor _$_
  field
    Pre : Set
    img : Pre -> X
open Fam public

{- Yes, it's covariant. -}
FAM : forall {X Y} -> (X -> Y) -> Fam X -> Fam Y
FAM f (P $ i) = P $ (i % f)

{-
Now, an arrow between Fams is a mediating map on
pre-images which respects the image maps.
-}
_=Fam>_ : forall {X} -> Fam X -> Fam X -> Set
(P $ i) =Fam> (Q $ j) =
  -- (P -> Q) >< \ f -> i ~ (f % j) {- not today! choice away! -}
  (p : P) -> Q >< \ q -> i p ~ j q

---------------------------------
-- What is (small) Pow? ---------
---------------------------------
{-
Pow is the contravariant proof-relevant power set functor.
Pow X picks a subset of X by "predicate" comprehension.
-}
Pow : Set -> Set1
Pow X = X -> Set

{- Yes, it's covariant. -}
POW : forall {X Y} -> (Y -> X) -> Pow X -> Pow Y
POW f P = f % P

{- Arrows between pows are "predicate" implications. -}
_=Pow>_ : forall {X} -> Pow X -> Pow X -> Set
P =Pow> Q = forall x -> P x -> Q x

--------------------------------------
-- Forgetful Interaction Structures --
--------------------------------------
record Interface : Set1 where
  constructor _!_/_
  field
    Memo : Set        -- what we remember
    Play : Fam Memo   -- how we can play
    Oppo : Pow Memo   -- how opponent can respond
open Interface public
{-
If Memo is 1, Play and Oppo amount to Set.
If Play is (Memo $ id), you have dependent interactions.
-}

{-
strategies achieving a goal by one step of interaction
-}
Step : (X : Interface) -> Set -> Set
Step (M ! P / O) G
  =  Pre P >< \ p        -- choose a play
  -> (o : O (img P p))   -- wait for a response
  -> G                   -- deliver the goal

------------------------------------------------------
-- morphisms between interfaces ----------------------
------------------------------------------------------
record _=>_ (S : Interface)(T : Interface) : Set where
  field
    translate : Memo S           ->       Memo T
    forwards  : FAM translate (Play S) =Fam> Play T
    backwards : POW translate (Oppo T) =Pow> Oppo S
open _=>_ public

{-
morphisms between interfaces transform strategies
-}
xform : forall {S T} -> S => T -> forall {G} -> Step S G -> Step T G
fst (xform F (p , r)) with p' , _ <- forwards F p = p'
snd (xform {S}{T} F (p , r)) o
  with p' , q <- forwards F p
     | back <- backwards F (img (Play S) p)
  rewrite q
     = r (back o)


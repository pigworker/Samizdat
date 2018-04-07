module Appl where

id : forall {l} {X : Set l} -> X -> X
id x = x

comp : forall {R S T : Set} -> (S -> T) -> (R -> S) -> R -> T
comp f g r = f (g r)

data _==_ {l}{X : Set l}(x : X) : X -> Set where
  refl : x == x
{-# BUILTIN EQUALITY _==_ #-}

trans : forall {l}{X : Set l}{x y z : X} -> x == y -> y == z -> x == z
trans refl q = q

cong : forall {l k}{X : Set l}{Y : Set k}(f : X -> Y) {x x' : X} -> x == x' -> f x == f x'
cong f refl = refl

record Appl (F : Set -> Set) : Set1 where
  field
    pure : {X : Set} -> X -> F X
    _<*>_ : {S T : Set} -> F (S -> T) -> F S -> F T
    homomorphism : forall {S T}(f : S -> T)(s : S) -> (pure f <*> pure s) == pure (f s)
    interchange  : forall {S T}(fF : F (S -> T))(s : S) -> (fF <*> pure s) == (pure (\ f -> f s) <*> fF)
    composition  : forall {R S T}(fF : F (S -> T))(gF : F (R -> S))(rF : F R) ->
                     (fF <*> (gF <*> rF)) == (((pure comp <*> fF) <*> gF) <*> rF)
    identity     : forall {X}(xF : F X) -> (pure id <*> xF) == xF

data Bwd {l}(X : Set l) : Set l where
  [] : Bwd X
  _-,_ : Bwd X -> X -> Bwd X

record One {l} : Set l where constructor <>

record Sg {l}(S : Set l)(T : S -> Set l) : Set l where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg
_*_ : forall {l} -> Set l -> Set l -> Set l
S * T = Sg S \ _ -> T

All : forall {k l}{X : Set l}(P : X -> Set k) -> Bwd X -> Set k
All P [] = One
All P (xz -, x) = All P xz * P x

_++_ : forall {l}{X : Set l} -> Bwd X -> Bwd X -> Bwd X
xz ++ [] = xz
xz ++ (yz -, x) = (xz ++ yz) -, x

pair : forall (Xz Yz : Bwd Set)(F : Set -> Set) -> All F Xz -> All F Yz -> All F (Xz ++ Yz)
pair Xz [] F xz <> = xz
pair Xz (Yz -, Y) F xz (yz , y) = pair Xz Yz F xz yz , y

split : forall (Xz Yz : Bwd Set)(F : Set -> Set)(xyz : All F (Xz ++ Yz)) -> All F Xz * All F Yz
split Xz [] F xyz = xyz , <>
split Xz (Yz -, Y) F (xyz , y) = let xz , yz = split Xz Yz F xyz in xz , ((yz , y))

module APPL (F : Set -> Set)(AF : Appl F) where
  open Appl AF

  run : (Xz : Bwd Set) -> All F Xz -> F (All id Xz)
  run [] <> = pure <>
  run (Xz -, X) (xz , x) = (pure _,_ <*> run Xz xz) <*> x

  data Appl' (T : Set) : Set1 where
    [_]     : F T -> Appl' T
    pure'   : T -> Appl' T
    _<*>'_  : forall {S} -> Appl' (S -> T) -> Appl' S -> Appl' T

  [!_!]0 : forall {T} -> Appl' T -> F T
  [! [ t ] !]0     = t
  [! pure' t !]0   = pure t
  [! f <*>' s !]0  = [! f !]0 <*> [! s !]0

  record NormA (T : Set) : Set1 where
    field
      Types  : Bwd Set
      report : All id Types -> T
      tasks  : All F Types
  open NormA

  nPure : forall {X} -> X -> NormA X
  nPure x = record { Types = [] ; report = \ _ -> x ; tasks = <> }

  splap : forall Az Bz {S T : Set} -> (All id Az -> S -> T) -> (All id Bz -> S) -> All id (Az ++ Bz) -> T
  splap Az Bz f s abz = let az , bz = split Az Bz id abz in f az (s bz)

  nApply : forall {S T} -> NormA (S -> T) -> NormA S -> NormA T
  nApply (record { Types = fAz ; report = f ; tasks = az }) record { Types = sBz ; report = s ; tasks = bz } =
    record { Types = fAz ++ sBz ; report = splap fAz sBz f s ; tasks = pair fAz sBz _ az bz }

  nOne : forall {T} -> F T -> NormA T
  nOne t = record { Types = [] -, _ ; report = snd ; tasks = <> , t }

  [!_!]N : forall {T} -> NormA T -> F T
  [! record { Types = Xz ; report = t ; tasks = xz } !]N = pure t <*> run Xz xz

  [!_!]1 : forall {T} -> Appl' T -> NormA T
  [! [ t' ] !]1 = nOne t'
  [! pure' t !]1 = nPure t
  [! f' <*>' s' !]1 = nApply [! f' !]1 [! s' !]1

  pc : forall {R S T} -> (f : S -> T)(gF : F (R -> S))(rF : F R) ->
         (pure f <*> (gF <*> rF)) == ((pure (comp f) <*> gF) <*> rF)
  pc {R}{S}{T} f gF rF rewrite composition (pure f) gF rF
                   | homomorphism {S -> T}{(R -> S) -> R -> T} (\ f g r -> f (g r)) f = refl

  ppc : forall {R S T} -> (f : S -> T)(g : R -> S)(rF : F R) ->
         (pure f <*> (pure g <*> rF)) == (pure (comp f g) <*> rF)
  ppc {R}{S}{T} f g rF rewrite pc f (pure g) rF | homomorphism (\ g r -> f (g r)) g = refl

  lemma : forall {S T} Az Bz (f : All id Az -> S -> T)(aFz : All F Az)(s : All id Bz -> S)(bFz : All F Bz) ->
            ((pure f <*> run Az aFz) <*> (pure s <*> run Bz bFz)) ==
            (pure (splap Az Bz f s) <*> run (Az ++ Bz) (pair Az Bz F aFz bFz))
  lemma Az [] f aFz s <>
    rewrite homomorphism s <>
          | interchange (pure f <*> run Az aFz) (s <>)
          | pc (\ f -> f (s <>)) (pure f) (run Az aFz)
          | homomorphism (\ g r -> g r (s <>)) f
          = refl
  lemma {S}{T} Az (Bz -, B) f aFz s (bFz , b)
    rewrite pc (splap Az (Bz -, B) f s) (pure _,_ <*> run (Az ++ Bz) (pair Az Bz F aFz bFz)) b
          | ppc (comp (splap Az (Bz -, B) f s)) _,_ (run (Az ++ Bz) (pair Az Bz F aFz bFz)) 
          | pc s (pure _,_ <*> run Bz bFz) b
          | composition (pure f <*> run Az aFz) (pure (comp s) <*> (pure _,_ <*> run Bz bFz)) b
          | ppc (comp s) _,_ (run Bz bFz)
          | ppc {All id Az}{S -> T}{(B -> S) -> B -> T} comp f (run Az aFz)
          | lemma Az Bz (comp comp f) aFz (comp (comp s) _,_) bFz
          = refl

  claim : forall {T}(a : Appl' T) -> [! a !]0 == [! [! a !]1 !]N
  claim {T} [ t ] rewrite homomorphism {One}{T -> _} _,_ <>
                        | composition {T}{One * T}{T} (pure snd) (pure (_,_ <>)) t
                        | homomorphism {One * T -> T}{(T -> One * T) -> _} (\ f g r -> f (g r)) snd
                        | homomorphism {T -> One * T}{T -> T} (\ g r -> snd (g r)) (_,_ <>)
                        | identity t = refl
  claim (pure' t) rewrite homomorphism {One}{_} (\ _ -> t) <> = refl
  claim (f' <*>' s') rewrite claim f' | claim s' = lemma (Types [! f' !]1) (Types [! s' !]1) (report [! f' !]1) (tasks [! f' !]1) (report [! s' !]1) (tasks [! s' !]1)

  solver : forall {T}(a b : Appl' T) -> [! a !]1 == [! b !]1 -> [! a !]0 == [! b !]0
  solver a b q rewrite claim a | claim b | q = refl
  

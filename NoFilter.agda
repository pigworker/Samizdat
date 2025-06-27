module NoFilter where

_-_ : forall {i j k}{A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k}
  (f : (a : A) -> B a)
  (g : {a : A} -> (b : B a) -> C a b)
  (a : A) -> C a (f a)
(f - g) a = g (f a)

data Nat : Set where
  ze : Nat
  su : Nat -> Nat

data _<=_ : Nat -> Nat -> Set where
  no : forall {n m} -> n <= m ->    n <= su m
  su : forall {n m} -> n <= m -> su n <= su m
  ze : ze <= ze
  
data Vec (X : Set) : Nat -> Set where
  [] : Vec X ze
  _,-_ : forall {n} -> X -> Vec X n -> Vec X (su n)

_<?_ : forall {X n m} -> n <= m -> Vec X m -> Vec X n
no th <? (x ,- xs) = th <? xs
su th <? (x ,- xs) = x ,- (th <? xs)
ze <? [] = []

data _<#>_ : forall {i j n} -> i <= n -> j <= n -> Set where
  nosu : forall {i j n}{th : i <= n}{ph : j <= n} -> th <#> ph -> no th <#> su ph
  suno : forall {i j n}{th : i <= n}{ph : j <= n} -> th <#> ph -> su th <#> no ph
  ze   : ze <#> ze

_!>_<!_ : forall {X i j n}{th : i <= n}{ph : j <= n}
  -> Vec X i -> th <#> ph -> Vec X j -> Vec X n
xs !> nosu p <! (x ,- ys) = x ,- (xs !> p <! ys)
(x ,- xs) !> suno p <! ys = x ,- (xs !> p <! ys)
[] !> ze <! [] = []

record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_ public

data Zeroey : Set where
record Zero : Set where
  constructor wrong
  field
    .bad : Zeroey
record One : Set where constructor <>
data Two : Set where ff tt : Two

_<ft>_ : forall {l}{P : Two -> Set l} -> P ff -> P tt -> (b : Two) -> P b
(f <ft> t) ff = f
(f <ft> t) tt = t

_*_ : Set -> Set -> Set
S * T = S >< \ _ -> T

_+_ : Set -> Set -> Set
S + T = Two >< (S <ft> T)

record Mebbes : Set1 where
  field
    Naw : Set
    Aye : Set
    wha : Naw + Aye
    .ain : Naw -> Aye -> Zero
open Mebbes public

[Vec_] : forall {X n} -> (X -> Set) -> Vec X n -> Set
[Vec P ] [] = One
[Vec P ] (x ,- xs) = P x * [Vec P ] xs

data Filter {X : Set}(D : X -> Mebbes){n : Nat} : Vec X n -> Set where
  filtered : forall {i j}{th : i <= n}{ph : j <= n}
    -> (ns : Vec X i)
    -> [Vec D - Naw ] ns
    -> (p : th <#> ph)
    -> (as : Vec X j)
    -> [Vec D - Aye ] as
    -> Filter D (ns !> p <! as)
    
filter : forall {X : Set}(D : X -> Mebbes){n : Nat}(xs : Vec X n) -> Filter D xs
filter D [] = filtered [] <> ze [] <>
filter D (x ,- xs) with D x .wha | filter D xs
... | ff , z | filtered ns np p as ap = filtered (x ,- ns) (z , np) (suno p) as ap
... | tt , z | filtered ns np p as ap = filtered ns np  (nosu p) (x ,- as) (z , ap)

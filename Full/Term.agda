module Term where

open import Basics
open import Cat

record Variant : Set where
  constructor va
  field
    hasSu   : Two
    hasBuDu : Two
    hasFu   : Two
open Variant public

data Fun : Variant -> Obj -> Obj -> Set where
  `id : forall {V X} -> Fun V X X
  `no : forall {V X} -> Fun V `0 X
  `ze : forall {V}   -> Fun V `1 `N
  `su : forall {b f} -> Fun (va tt b f) `N `N
  `du : forall {s f} -> Fun (va s tt f) `N `N
  `bu : forall {s f} -> Fun (va s tt f) `N `N
  `fu : forall {s b} -> Fun (va s b tt) `N `N

[_]F : {V : Variant} -> FARR (Fun V)
[ `id ]F = go id
[ `no ]F = go magic
[ `ze ]F = go (K- ze)
[ `su ]F = go su-_
[ `du ]F = go du-_
[ `bu ]F = go bu-_
[ `fu ]F = go fu-_

INJ : forall {A} -> FARR A -> Set
INJ {A} farra = forall {S T}(f : A S T) -> Inj (farra f)

dudu : Inj (go du-_)
dudu {ze} {ze} q = r~
dudu {su- x} {su- y} q with r~ <- dudu (natNoConf (natNoConf q)) = r~

bubu : Inj (go bu-_)
bubu q = dudu (natNoConf q)

fufu : Inj (go fu-_)
fufu {ze} {ze} q = r~
fufu {su- x} {su- y} q with r~ <- fufu (bubu q) = r~

funInj : {V : Variant} -> INJ ([_]F {V})
funInj `id q = q
funInj `ze q = r~
funInj `su q = natNoConf q
funInj `du q = dudu q
funInj `bu q = bubu q
funInj `fu q = fufu q

budu : {x y : Nat} -> bu- x ~ du- y -> Zero
budu {su- x} {su- y} q = budu (natNoConf (natNoConf q))

zedu : (x : Nat) -> ze ~ du- x -> x ~ ze
zedu ze q = r~

data Trouble : Obj -> Obj -> Set where
  `id : Trouble `1 `1
  `no : forall {X} -> Trouble `0 X
  `ze : Trouble `1 `N
  `fu : Trouble `N `N

[_]T : forall {s b S T} ->
       Trouble S T -> Fun (va s b tt) S T
[ `id ]T = `id
[ `no ]T = `no
[ `ze ]T = `ze
[ `fu ]T = `fu

f0g : forall {s b f S T} -> Fun (va ff ff ff) S T -> Fun (va s b f) S T
f0g `id = `id
f0g `no = `no
f0g `ze = `ze

f0gq :  forall {s b f S T}(g : Fun (va ff ff ff) S T)
  -> [ g ]F ~><~ [ f0g {s}{b}{f} g ]F
f0gq `id = _ [==]
f0gq `no = _ [==]
f0gq `ze = _ [==]

f1g : forall {s b S T} -> Fun (va ff ff tt) S T -> Fun (va s b tt) S T
f1g `id = `id
f1g `no = `no
f1g `ze = `ze
f1g `fu = `fu

f1gq :  forall {s b S T}(g : Fun (va ff ff tt) S T)
  -> [ g ]F ~><~ [ f1g {s}{b} g ]F
f1gq `id = _ [==]
f1gq `no = _ [==]
f1gq `ze = _ [==]
f1gq `fu = _ [==]

f2g : forall {s f S T} -> Fun (va ff tt ff) S T -> Fun (va s tt f) S T
f2g `id = `id
f2g `no = `no
f2g `ze = `ze
f2g `du = `du
f2g `bu = `bu

f2gq :  forall {s f S T}(g : Fun (va ff tt ff) S T)
  -> [ g ]F ~><~ [ f2g {s}{f} g ]F
f2gq `id = _ [==]
f2gq `no = _ [==]
f2gq `ze = _ [==]
f2gq `du = _ [==]
f2gq `bu = _ [==]

f6g : forall {S T} -> Fun (va tt tt ff) S T -> Fun (va tt tt tt) S T
f6g `id = `id
f6g `no = `no
f6g `ze = `ze
f6g `du = `du
f6g `bu = `bu
f6g `su = `su

f6gq :  forall {S T}(g : Fun (va tt tt ff) S T)
  -> [ g ]F ~><~ [ f6g g ]F
f6gq `id = _ [==]
f6gq `no = _ [==]
f6gq `ze = _ [==]
f6gq `du = _ [==]
f6gq `bu = _ [==]
f6gq `su = _ [==]


data FullEh : forall {S T} -> Fun (va ff ff tt) S T -> Set where
  isFull : FullEh `fu
  isDull : forall {S T}(f : Fun (va ff ff ff) S T) -> FullEh (f0g f)

fullEh : forall {S T} -> (f : Fun (va ff ff tt) S T) -> FullEh f
fullEh `id = isDull `id
fullEh `no = isDull `no
fullEh `ze = isDull `ze
fullEh `fu = isFull

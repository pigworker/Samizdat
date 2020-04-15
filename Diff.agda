module Diff where

data Nat : Set where ze : Nat ; su : Nat -> Nat

data Fin : Nat -> Set where
  ze : forall {n} -> Fin (su n)
  su : forall {n} -> Fin n -> Fin (su n)

data Flg : Set where nml dgn : Flg

data Reg : Flg -> Nat -> Set where
  -- the normal regulars
  #         : forall {f n} -> Fin n -> Reg f n
  `0 `1     : forall {f n} -> Reg f n
  _`+_ _`*_ : forall {f n} -> Reg f n -> Reg f n -> Reg f n
  `Mu       : forall {f n} -> Reg f (su n) -> Reg f n
  -- the degenerate regulars
  `wk       : forall {n}   -> Reg dgn n -> Reg dgn (su n)
  _`/_      : forall {n}   -> Reg dgn (su n) -> Reg dgn n -> Reg dgn n

-- everything can degenerate
degenerate : forall {f n} -> Reg f n -> Reg dgn n
degenerate (# x) = # x
degenerate `0 = `0
degenerate `1 = `1
degenerate (s `+ t) = degenerate s `+ degenerate t
degenerate (s `* t) = degenerate s `* degenerate t
degenerate (`Mu t) = `Mu (degenerate t)
degenerate (`wk t) = `wk t
degenerate (f `/ s) = f `/ s

module _
  (I : Nat -> Set)
  (bv : forall {n} -> I (su n))
  (wk : forall {n} -> I n -> I (su n))
  (tm : forall {n} -> I n -> Reg nml n)
  where
  lift : forall {n m} -> (Fin n -> I m) -> (Fin (su n) -> I (su m))
  lift f ze     = bv
  lift f (su i) = wk (f i)

  act : forall {n m} -> (Fin n -> I m) -> Reg nml n -> Reg nml m
  act al (# x) = tm (al x)
  act al `0 = `0
  act al `1 = `1
  act al (s `+ t) = act al s `+ act al t
  act al (s `* t) = act al s `* act al t
  act al (`Mu f) = `Mu (act (lift al) f)

ren = act Fin ze su #
sub = act (Reg nml) (# ze) (ren su) (\ t -> t)

_/_ : forall {n} -> Reg nml (su n) -> Reg nml n -> Reg nml n
f / s = sub (\ { ze -> s ; (su i) -> # i }) f

-- everything can be normalized
normalize : forall {f n} -> Reg f n -> Reg nml n
normalize (# x) = # x
normalize `0 = `0
normalize `1 = `1
normalize (s `+ t) = normalize s `+ normalize t
normalize (s `* t) = normalize s `* normalize t
normalize (`Mu f) = `Mu (normalize f)
normalize (`wk t) = ren su (normalize t)
normalize (f `/ s) = normalize f / normalize s

delta : forall {n f m} -> Fin n -> Fin n -> Reg f m
delta ze ze = `1
delta ze (su j) = `0
delta (su i) ze = `0
delta (su i) (su j) = delta i j

dbyd : forall {n} -> Fin n -> Reg dgn n -> Reg dgn n
dbyd x (# y) = delta x y
dbyd x `0 = `0
dbyd x `1 = `0
dbyd x (s `+ t) = dbyd x s `+ dbyd x t
dbyd x (s `* t) = (dbyd x s `* t) `+ (s `* dbyd x t)
dbyd x (`Mu f) =
  `Mu (`wk (dbyd (su x) f `/ `Mu f) `+
       (`wk (dbyd ze f `/ `Mu f) `* # ze))
dbyd ze (`wk t) = `0
dbyd (su x) (`wk t) = `wk (dbyd x t)
dbyd x (f `/ s) =
  (dbyd (su x) f `/ s) `+
  ((dbyd ze f `/ s) `* dbyd x s)

dbydn : forall {n} -> Fin n -> Reg nml n -> Reg nml n
dbydn x (# y) = delta x y
dbydn x `0 = `0
dbydn x `1 = `0
dbydn x (s `+ t) = dbydn x s `+ dbydn x t
dbydn x (s `* t) = (dbydn x s `* t) `+ (s `* dbydn x t)
dbydn x (`Mu f) =
  `Mu (ren su (dbydn (su x) f / `Mu f) `+
       (ren su (dbydn ze f / `Mu f) `* # ze))

data Zero : Set where
record One : Set where constructor <>
data Two : Set where ff tt : Two
record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_ public
_*_ _+_ : Set -> Set -> Set
S * T = S >< \ _ -> T
S + T = Two >< \ { ff -> S ; tt -> T }

data Mu (f : Reg nml (su ze)) : Set
[[_]] : Reg nml ze -> Set
data Mu f where
  <_> : [[ f / `Mu f ]] -> Mu f
[[ `0 ]]     = Zero
[[ `1 ]]     = One
[[ s `+ t ]] = [[ s ]] + [[ t ]]
[[ s `* t ]] = [[ s ]] * [[ t ]]
[[ `Mu f ]]  = Mu f


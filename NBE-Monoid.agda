module NBE-Monoid where

data _~_ {X : Set}(x : X) : X -> Set where
  r~ : x ~ x

data Zero : Set where
record One : Set where constructor <>
data Two : Set where ff tt : Two

data Fwd (X : Set) : Set where
  [] : Fwd X
  _,-_ : X -> Fwd X -> Fwd X

_>>>_ : {X : Set} -> Fwd X -> Fwd X -> Fwd X
[] >>> ys = ys
(x ,- xs) >>> ys = x ,- (xs >>> ys)

data Bwd (X : Set) : Set where
  []   : Bwd X
  _-,_ : Bwd X -> X -> Bwd X

record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_ public

_*_ : Set -> Set -> Set
S * T = S >< \ _ -> T

_<ft>_ : forall {l}{P : Two -> Set l} -> P ff -> P tt -> (b : Two) -> P b
(f <ft> t) ff = f
(f <ft> t) tt = t

_+_ : Set -> Set -> Set
S + T = Two >< (S <ft> T)

not : Two -> Two
not ff = tt
not tt = ff

Diff : Two -> Two -> Set
Diff ff ff = Zero
Diff ff tt = One
Diff tt ff = One
Diff tt tt = Zero

data Sod (b : Two) : Two -> Set where
  same : Sod b b
  diff : forall {x} -> .(d : Diff b x) -> Sod b x
sod : forall b x -> Sod b x
sod ff ff = same
sod ff tt = diff <>
sod tt ff = diff <>
sod tt tt = same

data Ord : Set where LT EQ GT : Ord

lexic : Ord -> Ord -> Ord
lexic LT _ = LT
lexic EQ o = o
lexic GT _ = GT

module _ {X : Set}(cmp : X -> X -> Ord)(glu : X -> Fwd X -> Fwd X) where
  insert : X -> Fwd X -> Fwd X
  insert x [] = x ,- []
  insert x (y ,- ys) with cmp x y
  ... | LT = x ,- (y ,- ys)
  ... | EQ = glu x ys
  ... | GT = y ,- insert x ys
  merge : Fwd X -> Fwd X -> Fwd X
  merge [] ys = ys
  merge (x ,- xs) ys = insert x (merge xs ys)

{-
merge cmp glu (x ,- xs) (y ,- ys) with cmp x y
... | LT = x ,- merge cmp glu xs (y ,- ys)
... | EQ = glu x (merge cmp glu xs ys)
... | GT = y ,- merge cmp glu (x ,- xs) ys
merge cmp glu [] ys = ys
merge cmp glu xs [] = xs
-}
module _ {X : Set} where

  data _<=_ : Bwd X -> Bwd X -> Set where
    _-^_ : forall {ga de} -> ga <= de -> forall s -> ga <= (de -, s)
    _-,_ : forall {ga de} -> ga <= de -> forall s -> (ga -, s) <= (de -, s)
    []   : [] <= []
  infixl 10 _-,_ _-^_

  no : forall {ga} -> [] <= ga
  no {[]} = []
  no {ga -, x} = no {ga} -^ x

  io : forall {ga} -> ga <= ga
  io {[]} = []
  io {ga -, x} = io {ga} -, x

  _-<_ : forall {ga de xi} -> ga <= de -> de <= xi -> ga <= xi
  th -< (ph -^ s) = (th -< ph) -^ s
  (th -^ .s) -< (ph -, s) = (th -< ph) -^ s
  (th -, .s) -< (ph -, s) = (th -< ph) -, s
  [] -< [] = []

  thOrd : forall {De Xi Ga Om} -> De <= Ga -> Xi <= Om -> Ord
  thOrd (th -^ _) (ph -^ _) = thOrd th ph
  thOrd (th -^ _) (ph -, _) = GT
  thOrd (th -^ _) [] = GT
  thOrd (th -, _) (ph -^ _) = LT
  thOrd (th -, _) (ph -, _) = thOrd th ph
  thOrd (th -, _) [] = GT
  thOrd [] (ph -^ s) = LT
  thOrd [] (ph -, s) = LT
  thOrd [] [] = EQ

data Ty : Set where
  `0 `1 `2   : Ty
  Li         : Ty -> Ty
  _`*_ _`->_ : Ty -> Ty -> Ty

data Mon : Ty -> Set where
  M1 : Mon `1
  MV : Two -> Mon `2
  MX : Two -> Mon `2
  MF : (T : Ty) -> Mon (Li T)
  MA : (T : Ty) -> Mon (T `-> T)
  ML : (S : Ty){T : Ty}(M : Mon T) -> Mon (S `-> T)
  MP : {S T : Ty} -> (M : Mon S)(N : Mon T) -> Mon (S `* T)

data _!=_ (Ga : Bwd Ty) : {T : Ty} -> Mon T -> Set
data _!-_ (Ga : Bwd Ty) : Ty -> Set where
  va : forall {T} -> ([] -, T) <= Ga -> Ga !- T
  mo : {T : Ty}(M : Mon T) -> Ga != M -> Ga !- T
  <> : Ga !- `1
  bo : Two -> Ga !- `2
  if : forall {T} -> Ga !- `2 -> Ga !- T -> Ga !- T -> Ga !- T
  pa : forall {S T} -> Ga !- S -> Ga !- T -> Ga !- (S `* T)
  pl : forall {S T} -> Ga !- (S `* T) -> Ga !- S
  pr : forall {S T} -> Ga !- (S `* T) -> Ga !- T
  la : forall {S T} -> (Ga -, S) !- T -> Ga !- (S `-> T)
  ap : forall {S T} -> Ga !- (S `-> T) -> Ga !- S -> Ga !- T

data _!=_ Ga where
  elt : forall {T}{M : Mon T} -> Ga !- T -> Ga != M
  neu : forall {T}{M : Mon T} -> Ga != M
  cat : forall {T}{M : Mon T} -> Ga != M -> Ga != M -> Ga != M
  non : forall {M : Mon `2} -> Ga != M
  one : forall {T} -> Ga !- T -> Ga != MF T
  act : forall {T} -> Ga !- (T `-> T) -> Ga != MA T
  lam : forall {S T}{M : Mon T} -> (Ga -, S) != M -> Ga != (ML S M)
  twa : forall {S T}{M : Mon S}{N : Mon T}
     -> Ga != M -> Ga != N -> Ga != MP M N
  cru : forall {S T}{M : Mon T}
     -> Ga != MF S -> (Ga -, S) != M -> Ga != M

data Nat : Set where
  ze : Nat
  su : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

natOrd : Nat -> Nat -> Ord
natOrd ze ze = EQ
natOrd ze (su y) = LT
natOrd (su x) ze = GT
natOrd (su x) (su y) = natOrd x y

twoOrd : Two -> Two -> Ord
twoOrd ff ff = EQ
twoOrd ff tt = LT
twoOrd tt ff = GT
twoOrd tt tt = EQ

tyOrd : Ty -> Ty -> Ord
tyOrd (Li S) (Li T) = tyOrd S T
tyOrd (S `* U) (T `* V) = lexic (tyOrd S T) (tyOrd U V)
tyOrd (S `-> U) (T `-> V) = lexic (tyOrd S T) (tyOrd U V)
tyOrd S T = natOrd (tc S) (tc T) where
  tc : Ty -> Nat
  tc `0 = 0
  tc `1 = 1
  tc `2 = 2
  tc (Li _) = 3
  tc (_ `* _) = 4
  tc (_ `-> _) = 5

monOrd : forall {S T} -> Mon S -> Mon T -> Ord
monOrd (MV a) (MV b) = twoOrd a b
monOrd (MX a) (MX b) = twoOrd a b
monOrd (MF S) (MF T) = tyOrd S T
monOrd (MA S) (MA T) = tyOrd S T
monOrd (ML S M) (ML T N) = lexic (tyOrd S T) (monOrd M N)
monOrd (MP M O) (MP N P) = lexic (monOrd M N) (monOrd O P)
monOrd M N = natOrd (mc M) (mc N) where
  mc : forall {T} -> Mon T -> Nat
  mc M1 = 0
  mc (MV _) = 1
  mc (MX _) = 2
  mc (MF _) = 3
  mc (MA _) = 4
  mc (ML _ _) = 5
  mc (MP _ _) = 6

tmOrd : forall {Ga De S T} -> Ga !- S -> De !- T -> Ord
moOrd : forall {Ga De S T}{M : Mon S}{N : Mon T} -> Ga != M -> De != N -> Ord
tmOrd (va x) (va y) = thOrd x y
tmOrd (mo M x) (mo N y) = lexic (monOrd M N) (moOrd x y)
tmOrd (bo ff) (bo ff) = EQ
tmOrd (bo ff) (bo tt) = LT
tmOrd (bo tt) (bo ff) = GT
tmOrd (bo tt) (bo tt) = EQ
tmOrd (if a t f) (if b u g) = lexic (tmOrd a b) (lexic (tmOrd t u) (tmOrd f g))
tmOrd (pa a c) (pa b d) = lexic (tmOrd a b) (tmOrd c d)
tmOrd (pl a) (pl b) = tmOrd a b
tmOrd (pr a) (pr b) = tmOrd a b
tmOrd (la a) (la b) = tmOrd a b
tmOrd (ap f a) (ap g b) = lexic (tmOrd f g) (tmOrd a b)
tmOrd a b = natOrd (cx a) (cx b) where
  cx : forall {Ga T} -> Ga !- T -> Nat
  cx (va x) = 0
  cx (mo _ _) = 1
  cx <> = 2
  cx (bo _) = 3
  cx (if _ _ _) = 4
  cx (pa _ _) = 5
  cx (pl _) = 6
  cx (pr _) = 7
  cx (la _) = 8
  cx (ap _ _) = 9
moOrd (elt x) (elt y) = tmOrd x y
moOrd (cat m o) (cat n p) = lexic (moOrd m n) (moOrd o p)
moOrd (one x) (one y) = tmOrd x y
moOrd (act x) (act y) = tmOrd x y
moOrd (lam m) (lam n) = moOrd m n
moOrd (twa m o) (twa n p) = lexic (moOrd m n) (moOrd o p)
moOrd (cru m o) (cru n p) = lexic (moOrd m n) (moOrd o p)
moOrd x y = natOrd (mc x) (mc y) where
  mc : forall {Ga T}{M : Mon T} -> Ga != M -> Nat
  mc neu = 0
  mc (elt _) = 1
  mc (cat _ _) = 2
  mc non = 3
  mc (one _) = 4
  mc (act _) = 5
  mc (lam _) = 6
  mc (twa _ _) = 7
  mc (cru _ _) = 8

_^t_ : forall {Ga De T} -> Ga !- T -> Ga <= De -> De !- T
_^m_ : forall {Ga De T}{M : Mon T} -> Ga != M -> Ga <= De -> De != M
va x ^t th = va (x -< th)
mo M m ^t th = mo M (m ^m th)
<> ^t th = <>
bo b ^t th = bo b
if b t f ^t th = if (b ^t th) (t ^t th) (f ^t th)
pa s t ^t th = pa (s ^t th) (t ^t th)
pl p ^t th = pl (p ^t th)
pr p ^t th = pr (p ^t th)
la t ^t th = la (t ^t (th -, _))
ap f s ^t th = ap (f ^t th) (s ^t th)
elt t ^m th = elt (t ^t th)
neu ^m th = neu
cat m n ^m th = cat (m ^m th) (n ^m th)
non ^m th = non
one t ^m th = one (t ^t th)
act f ^m th = act (f ^t th)
lam m ^m th = lam (m ^m (th -, _))
twa m n ^m th = twa (m ^m th) (n ^m th)
cru m n ^m th = cru (m ^m th) (n ^m (th -, _))

Val Neu Can : Bwd Ty -> Ty -> Set
Val Ga T = Neu Ga T + Can Ga T
Neu Ga `0 = Ga !- `0
Neu Ga `1 = Zero
Neu Ga `2 = Ga !- `2
Neu Ga (Li T) = Zero
Neu Ga (S `* T) = Zero
Neu Ga (S `-> T) = Zero
Can Ga `0 = Zero
Can Ga `1 = One
Can Ga `2 = Two
Can Ga (Li T) = Fwd ((Ga !- Li T) + Val Ga T)
Can Ga (S `* T) = Val Ga S * Val Ga T
Can Ga (S `-> T) = forall De -> Ga <= De -> Val De S -> Val De T

glom : forall {Ga}{M : Mon `2} -> Ga !- `2 -> Fwd (Ga !- `2) -> Ga != M
glom x [] = elt x
glom x (y ,- zs) = cat (elt x) (glom y zs)

wVal : forall {Ga De} T -> Val Ga T -> Ga <= De -> Val De T
wCan : forall {Ga De} T -> Can Ga T -> Ga <= De -> Can De T
wNeu : forall {Ga De} T -> Neu Ga T -> Ga <= De -> Neu De T
wVal T (ff , t) th = ff , wNeu T t th
wVal T (tt , t) th = tt , wCan T t th
wNeu `0 t th = t ^t th
wNeu `2 t th = t ^t th
wCan `1 t th = <>
wCan `2 b th = b
wCan {Ga}{De} (Li T) ts th = go ts where
  go : Fwd ((Ga !- Li T) + Val Ga T) -> Fwd ((De !- Li T) + Val De T)
  go [] = []
  go (t ,- ts) = ho t ,- go ts where
    ho : (Ga !- Li T) + Val Ga T -> (De !- Li T) + Val De T
    ho (ff , t) = ff , (t ^t th)
    ho (tt , t) = tt , wVal T t th
wCan (S `* T) (s , t) th = wVal S s th , wVal T t th
wCan (S `-> T) f th Xi ph s = f Xi (th -< ph) s

MVal : Bwd Ty -> {T : Ty} -> Mon T -> Set
MVal Ga M1 = One
MVal Ga (MV n) = Fwd (Ga !- `2) + One
MVal Ga (MX x) = Two  -- neutral?
               * Fwd (Ga !- `2)
MVal Ga (MF T) = Can Ga (Li T)
MVal Ga (MA T) = Can Ga (T `-> T)
MVal Ga (ML S M) = forall De -> Ga <= De -> Val De S -> MVal De M
MVal Ga (MP M N) = MVal Ga M * MVal Ga N

unq : forall {Ga} T -> Ga !- T -> Val Ga T
quo : forall {Ga} T -> Val Ga T -> Ga !- T

unq `0 t = ff , t
unq `1 t = tt , <>
unq `2 t = ff , t
unq (Li T) t = tt , ((ff , t) ,- [])
unq (S `* T) p = tt , (unq S (pl p) , unq T (pr p))
unq (S `-> T) f = tt , \ De th s -> unq T (ap (f ^t th) (quo S s))

quo `0 (ff , t) = t
quo `1 t = <>
quo `2 (ff , t) = t
quo `2 (tt , b) = bo b
quo {Ga} (Li T) (tt , ts) = mo (MF T) (go ts) where
  ho : (Ga !- Li T) + Val Ga T -> Ga != MF T
  ho (ff , x) = elt x
  ho (tt , x) = one (quo T x)
  go : Fwd ((Ga !- Li T) + Val Ga T) -> Ga != MF T
  go [] = neu
  go (v ,- vs) with ho v
  go (v ,- []) | t = t
  go (v ,- (w ,- vs)) | t = cat t (go (w ,- vs))
quo (S `* T) (tt , (s , t)) = pa (quo S s) (quo T t)
quo (S `-> T) (tt , f) = la (quo T (f _ (io -^ S) (unq S (va (no -, S)))))

bits : forall {Ga}{M : Mon `2} ->
  Ga !- `2 -> Fwd (Ga !- `2) -> Ga != M
bits x [] = elt x
bits x (y ,- zs) = cat (elt x) (bits y zs)

quom : forall {Ga T}(M : Mon T) -> MVal Ga M -> Ga != M
quom M1 v = neu
quom (MV n) (ff , []) = neu
quom {Ga} (MV n) (ff , (x ,- xs)) = bits x xs
quom (MV n) (tt , <>) = non
quom (MX n) (ff , []) = non
quom (MX n) (ff , (x ,- xs)) = cat non (bits x xs)
quom (MX n) (tt , []) = neu
quom (MX n) (tt , (x ,- xs)) = bits x xs
quom {Ga} (MF T) ts = go ts where
  go : Fwd ((Ga !- Li T) + Val Ga T) -> Ga != MF T
  go [] = neu
  go (v ,- vs) = cat (ho v) (go vs) where
    ho : (Ga !- Li T) + Val Ga T -> Ga != MF T
    ho (ff , x) = elt x
    ho (tt , x) = one (quo T x)
quom (MA T) v = act (quo (T `-> T) (tt , v))
quom (ML S M) f = lam (quom M (f _ (io -^ _) (unq S (va (no -, S)))))
quom (MP M N) (s , t) = twa (quom M s) (quom N t)

mov : forall {Ga T}(M : Mon T) -> MVal Ga M -> Val Ga T
mov M1 v = tt , <>
mov (MV n) (ff , []) = tt , n
mov {Ga} (MV n) (ff , (x ,- xs)) = ff , mo (MV n) (glom x xs)
mov (MV n) (tt , <>) = tt , not n
mov (MX n) (ff , []) = tt , not n
mov (MX n) (tt , []) = tt , n
mov {Ga} (MX n) (ff , (x ,- xs)) = ff , mo (MX n) (cat non (glom x xs))
mov {Ga} (MX n) (tt , (x ,- xs)) = ff , mo (MX n) (glom x xs)
mov (MF T) v = tt , v
mov (MA T) v = tt , v
mov (ML S M) v = tt , \ De th s -> mov M (v De th s)
mov (MP M N) (s , t) = tt , (mov M s , mov N t)

neutral : forall {Ga T}(M : Mon T) -> MVal Ga M
neutral M1 = <>
neutral (MV x) = ff , []
neutral (MX n) = n , []
neutral (MF T) = []
neutral (MA T) De th t = t
neutral (ML S M) De th s = neutral M
neutral (MP M N) = neutral M , neutral N

concatenate : forall {Ga T}(M : Mon T) -> MVal Ga M -> MVal Ga M -> MVal Ga M
concatenate M1 <> <> = <>
concatenate (MV n) (ff , x) (ff , y) = ff , merge tmOrd _,-_ x y
concatenate (MV n) (ff , x) (tt , y) = tt , <>
concatenate (MV n) (tt , <>) (c , y) = tt , <>
concatenate (MX n) (ff , x) (c , y) = not c , merge tmOrd (\ _ xs -> xs) x y
concatenate (MX n) (tt , x) (c , y) = c , merge tmOrd (\ _ xs -> xs) x y
concatenate (MF T) x y = x >>> y
concatenate (MA T) f g De th t = f De th (g De th t)
concatenate (ML S M) f g De th s = concatenate M (f De th s) (g De th s)
concatenate (MP M N) (xm , xn) (ym , yn) = concatenate M xm ym , concatenate N xn yn

element : forall {Ga T}(M : Mon T) -> Val Ga T -> MVal Ga M
element M1 v = <>
element (MV n) (ff , v) = ff , (v ,- [])
element (MV n) (tt , b) with sod n b
... | same = ff , []
... | diff d = tt , <>
element (MX n) (ff , v) = tt , (v ,- [])
element (MX n) (tt , b) with sod n b
... | same = tt , []
... | diff d = ff , []
element (MF T) (tt , v) = v
element (MA T) (tt , v) = v
element (ML S M) (tt , f) De th s = element M (f De th s)
element (MP M N) (tt , (u , v)) = element M u , element N v

val : forall {Ga De} T -> Ga !- T -> (forall {S} -> ([] -, S) <= Ga -> Val De S)
   -> Val De T
mon : forall {Ga De T}(M : Mon T) -> Ga != M -> (forall {S} -> ([] -, S) <= Ga -> Val De S)
   -> MVal De M
   
val T (va x) ga = ga x
val T (mo M m) ga = mov M (mon M m ga)
val .`1 <> ga = tt , <>
val .`2 (bo b) ga = tt , b
val T (if b t f) ga with val `2 b ga
... | ff , b = unq T (if b (quo T (val T t ga)) (quo T (val T f ga)))
... | tt , ff = val T f ga
... | tt , tt = val T t ga
val (S `* T) (pa s t) ga = tt , (val S s ga , val T t ga)
val T (pl tm) ga with val _ tm ga
... | tt , (l , r) = l
val T (pr tm) ga with val _ tm ga
... | tt , (l , r) = r
val (S `-> T) (la tm) ga = tt , \ Xi th s -> val T tm 
  \ { (x -^ .S) -> wVal _ (ga x) th
    ; (x -, .S) -> s
    }
val T (ap f s) ga with val _ f ga
... | tt , f = f _ io (val _ s ga)

mon M (elt x) ga = element M (val _ x ga)
mon M neu ga = neutral M
mon M (cat m n) ga = concatenate M (mon M m ga) (mon M n ga)
mon (MV x) non ga = tt , <>
mon (MX x) non ga = ff , []
mon .(MF _) (one t) ga = (tt , val _ t ga) ,- []
mon (MA T) (act f) ga with val (T `-> T) f ga
... | tt , g = g
mon (ML S M) (lam m) ga De th s = mon M m 
  \ { (x -^ .S) -> wVal  _ (ga x) th
    ; (x -, .S) -> s
    }
mon (MP M N) (twa m n) ga = mon M m ga , mon N n ga
mon {Ga}{De} M (cru {S} m f) ga = go (mon (MF S) m ga) where
  me : (De !- Li S) + Val De S -> MVal De M
  me (ff , v) = element M (unq _ (mo M (cru (elt v) (quom M (mon M f 
     \ { (x -^ .S) -> wVal _ (ga x) (io -^ S)
       ; (x -, .S) -> unq _ (va (no -, S))
       })))))
  me (tt , s) = mon M f \
    { (x -^ .S) -> ga x
    ; (x -, .S) -> s
    }
  go : Fwd ((De !- Li S) + Val De S) -> MVal De M
  ho : MVal De M -> Fwd ((De !- Li S) + Val De S) -> MVal De M
  go [] = neutral M
  go (s ,- ss) = ho (me s) ss
  ho m [] = m
  ho m (s ,- ss) = concatenate M m (go (s ,- ss))

idEnv : forall {Ga S} -> ([] -, S) <= Ga -> Val Ga S
idEnv (x -^ S) = wVal _ (idEnv x) (io -^ S)
idEnv (x -, S) = unq _ (va (no -, S))

quev : forall {Ga T} -> Ga !- T -> Ga !- T
quev {Ga}{T} t = quo T (val T t idEnv)


-- quev (mo (MV tt) (cat (elt (va (no -, `2))) non))
-- quev (mo (MV tt) (cat (elt (va (no {_}{[]} -, `2))) (elt (va (no -, `2)))))
-- quev (mo (MX tt) (cat (elt (va (no -, `2))) non))
-- quev (mo (MX tt) (cat (elt (va (no {_}{[]} -, `2))) (elt (va (no -, `2)))))
-- quev (mo (MF `2) (cat (cat (elt (va (no -, _))) (elt (va (no -, _ -^ _)))) (cat neu (elt (va (no -, _ -^ _ -^ _))))))
-- quev (mo (MV tt) (cat (elt (va (no{_}{[]} -^ _ -, _))) (elt (va (no{_}{[]} -, _ -^ _)))))
-- quev (mo (MV tt) (cat (elt (va (no{_}{[]} -, _ -^ _))) (elt (va (no{_}{[]} -^ _ -, _)))))

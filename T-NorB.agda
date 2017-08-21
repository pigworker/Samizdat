module T-NorB where

data Nat : Set where
  ze : Nat
  su : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

data Dir : Set where chk syn : Dir

data Bwd (X : Set) : Set where
  [] : Bwd X
  _-,_ : Bwd X -> X -> Bwd X

data BVec (X : Set) : Nat -> Set where
  [] : BVec X ze
  _-,_ : {n : Nat} -> BVec X n -> X -> BVec X (su n)

infixl 3 _-,_

data Ty : Set where
  nat bool : Ty
  _=>_ : Ty -> Ty -> Ty

infixr 4 _=>_

data _<=_ : Nat -> Nat -> Set where
  oz : ze <= ze
  os : {n m : Nat} -> n <= m -> su n <= su m
  o' : {n m : Nat} -> n <= m ->    n <= su m

_-<-_ : forall {p n m} -> p <= n -> n <= m -> p <= m
f -<- o' g = o' (f -<- g)
oz -<- oz = oz
os f -<- os g = os (f -<- g)
o' f -<- os g = o' (f -<- g)

oi : forall {n} -> n <= n
oi {ze} = oz
oi {su x} = os oi

on : forall {n} -> ze <= n
on {ze} = oz
on {su x} = o' on

_/_ : forall {X n} -> BVec X n -> 1 <= n -> X
[] / ()
(xz -, x) / os _ = x
(xz -, x) / o' i = xz / i

data Tm (n : Nat) : Dir -> Set where
  [_]  : Tm n syn -> Tm n chk
  lam  : Tm (su n) chk -> Tm n chk
  _%_  : Nat -> Bwd (Tm n chk) -> Tm n chk
  #    : 1 <= n -> Tm n syn
  _$_  : Tm n syn -> Tm n chk -> Tm n syn
  rec  : Tm n syn -> Ty -> Tm n chk -> Tm n chk -> Tm n syn
  _::_ : Tm n chk -> Ty -> Tm n syn
infixl 4 _$_
infixr 2 _%_

_^_ : forall {n m d} -> Tm n d -> n <= m -> Tm m d
_^z_ : forall {n m d} -> Bwd (Tm n d) -> n <= m -> Bwd (Tm m d)
[ t ] ^ r = [ t ^ r ]
lam t ^ r = lam (t ^ os r)
(c % tz) ^ r = c % (tz ^z r)
# i ^ r = # (i -<- r)
(f $ s) ^ r = (f ^ r) $ (s ^ r)
rec e T t t' ^ r = rec (e ^ r) T (t ^ r) (t' ^ r)
(t :: T) ^ r = (t ^ r) :: T

[] ^z r = []
(tz -, t) ^z r = (tz ^z r) -, (t ^ r)

data _+_ (S T : Set) : Set where
  inl : S -> S + T
  inr : T -> S + T

data Maybe (X : Set) : Set where
  yes : X -> Maybe X
  no : Maybe X

data Two : Set where
  tt ff : Two
record One : Set where constructor <>
record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg
_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T

Va Go : Ty -> Nat -> Set
Va T n = Tm n syn + Go T n
Go nat       n = Nat * (One + Tm n syn)
Go bool      n = Two
Go (S => T)  n = {m : Nat} -> n <= m -> Va S m -> Maybe (Va T m)

_!_^^_ : forall T {n m} -> Va T n -> n <= m -> Va T m
T ! inl e ^^ r = inl (e ^ r)
nat  ! inr (n , inl <>) ^^ r = inr (n , inl <>)
nat  ! inr (n , inr e)  ^^ r = inr (n , inr (e ^ r))
bool ! inr tt ^^ r = inr tt
bool ! inr ff ^^ r = inr ff
(S => T) ! inr g ^^ r = inr \ r' s -> g (r -<- r') s

Cell : Nat -> Set
Cell n = Sg Ty \ T -> Va T n

_^C_ : forall {n m} -> Cell n -> n <= m -> Cell m
(T , v) ^C r = T , (T ! v ^^ r)

Env : Nat -> Nat -> Set
Env n l = BVec (Cell l) n

_^E_ : forall {n m l} -> Env l n -> n <= m -> Env l m
[] ^E r = []
(g -, c) ^E r = (g ^E r) -, (c ^C r)

_>>=_ : {S T : Set} -> Maybe S -> (S -> Maybe T) -> Maybe T
no >>= k = no
yes s >>= k = k s

data _==_ {X : Set}(x : X) : X -> Set where
  refl : x == x

tyQ? : (S T : Ty) -> Maybe (S == T)
tyQ? nat nat = yes refl
tyQ? nat bool = no
tyQ? nat (_ => _) = no
tyQ? bool nat = no
tyQ? bool bool = yes refl
tyQ? bool (_ => _) = no
tyQ? (_ => _) nat = no
tyQ? (_ => _) bool = no
tyQ? (S => T) (S' => T') with tyQ? S S' | tyQ? T T'
tyQ? (S => T) (.S => .T) | yes refl | yes refl = yes refl
tyQ? (S => T) (S' => T') | _ | _ = no

sucs : Nat -> forall {m} -> Tm m chk -> Tm m chk
sucs ze t = t
sucs (su n) t = 1 % ([] -, sucs n t)

stop : forall T {l} -> Va T l -> Maybe (Tm l chk)
stop T (inl e) = yes [ e ]
stop nat (inr (n , inl <>)) = yes (sucs n (0 % []))
stop nat (inr (n , inr e)) = yes (sucs n [ e ])
stop bool (inr tt) = yes (1 % [])
stop bool (inr ff) = yes (0 % [])
stop (S => T) (inr g) =
  g (o' oi) (inl (# (os on))) >>= \ v ->
  stop T v >>= \ t ->
  yes (lam t)

apply : forall S T {l} -> Va (S => T) l -> Va S l -> Maybe (Va T l)
apply S T (inl f) u = stop S u >>= \ s -> yes (inl (f $ s))
apply S T (inr g) u = g oi u

primRec : {l : Nat}(T : Ty) -> Va nat l ->
  Maybe (Va T l) -> Maybe (Va (nat => T => T) l) -> 
  Maybe (Cell l)
primRec T (inl e) (yes vz) ms =
  stop T vz >>= \ tz ->
  ms >>= \ vs -> stop (nat => T => T) vs >>= \ ts ->
  yes (T , inl (rec e T tz ts))
primRec {l} T (inr (n , t)) (yes vz) ms =
  go n t >>= \ v -> yes (T , v)
 where
  go : Nat -> (One + Tm l syn) -> Maybe (Va T l)
  go ze (inl <>) = yes vz
  go ze (inr e)  =
    stop T vz >>= \ tz ->
    ms >>= \ vs -> stop (nat => T => T) vs >>= \ ts ->
    yes (inl (rec e T tz ts))
  go (su n) t = go n t >>= \ v -> ms >>= \ vs ->
    apply nat (T => T) vs (inr (n , t)) >>= \ vf ->
    apply T T vf v
primRec _ _ _ _ = no

chkEval : {n l : Nat} -> Env n l ->
          (T : Ty) -> Tm n chk -> Maybe (Va T l)
evalSyn : {n l : Nat} -> Env n l ->
          Tm n syn -> Maybe (Cell l)
chkEval g T [ e ] with evalSyn g e
chkEval g T [ e ] | no = no
chkEval g T [ e ] | yes (S , v) with tyQ? S T
chkEval g .S [ e ] | yes (S , v) | (yes refl) = yes v
chkEval g T [ e ] | yes (S , v) | no = no
chkEval g nat (lam t) = no
chkEval g bool (lam t) = no
chkEval g (S => T) (lam t) =
  yes (inr (\ r s -> chkEval ((g ^E r) -, (S , s)) T t))
chkEval g nat (0 % []) = yes (inr (ze , inl <>))
chkEval g nat (1 % [] -, n) = chkEval g nat n >>=
  \ { (inl e) -> yes (inr (1 , inr e))
    ; (inr (n , t)) -> yes (inr (su n , t))}
chkEval g bool (0 % []) = yes (inr ff)
chkEval g bool (1 % []) = yes (inr tt)
chkEval g _ (c % tz) = no
evalSyn g (# i) = yes (g / i)
evalSyn g (f $ s) = evalSyn g f >>=
  \ { ((S => T) , v) -> chkEval g S s
       >>= \ u -> apply S T v u >>= \ w -> yes (T , w)
    ; _ -> no }
evalSyn g (rec e T t0 t1) with evalSyn g e
evalSyn g (rec e T t0 t1) | yes (nat , v) =
  primRec T v (chkEval g T t0) (chkEval g (nat => T => T) t1)
evalSyn g (rec e T t0 t1) | yes (bool , inl e') =
  chkEval g T t0 >>= \ v0 -> stop T v0 >>= \ n0 ->
  chkEval g T t1 >>= \ v1 -> stop T v1 >>= \ n1 ->
  yes (T , inl (rec e' T n0 n1)) 
evalSyn g (rec e T t0 t1) | yes (bool , inr tt) =
  chkEval g T t1 >>= \ v -> yes (T , v)
evalSyn g (rec e T t0 t1) | yes (bool , inr ff) =
  chkEval g T t0 >>= \ v -> yes (T , v)
... | _ = no
evalSyn g (t :: T) = chkEval g T t >>= \ v -> yes (T , v)

add : forall {n} -> Tm n syn
add = lam (lam [ rec (# (o' (os on))) nat
                 [ # (os on) ]
                 (lam (lam (1 % [] -, [ # (os on) ]))) ])
      :: (nat => nat => nat)
vNat : Nat -> forall {n} -> Tm n chk
vNat ze = 0 % []
vNat (su n) = 1 % [] -, vNat n

natQ : forall {n} -> Tm n syn
natQ = lam [ rec (# (os on)) (nat => bool)
  (lam [ rec (# (os on)) bool
    (1 % [])
    (lam (lam (0 % []))) ])
  (lam (lam (lam [ rec (# (os on)) bool
    (0 % [])
    (lam (lam [ # (o' (o' (o' (os on))))
                  $ [ # (o' (os on)) ] ])) ])))
  ] :: (nat => nat => bool)
  
test : Maybe (Cell ze)
test = evalSyn [] (natQ $ [ add $ vNat 2 $ vNat 2 ] $ vNat 4)

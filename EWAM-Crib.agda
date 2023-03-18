module EWAM-Crib where


data Nat : Set where
  ze : Nat
  su : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

natElim : forall {l}
  (n : Nat)                           -- target
  (P : Nat -> Set l)                  -- motive
  (z : P ze)                          -- methods
  (s : (k : Nat) -> P k -> P (su k))
  ->
  P n -- the return type is an instance of the motive

natElim ze     P z s = z
natElim (su k) P z s = s k (natElim k P z s)

natCase : forall {l}
  (n : Nat)                           -- target
  (P : Nat -> Set l)                  -- motive
  (z : P ze)                          -- methods
  (s : (k : Nat) -> P (su k))
  ->
  P n -- the return type is an instance of the motive
natCase n P z s = natElim n P z \ k kh -> s k

{-
plus : Nat -> Nat -> Nat
plus = \ x -> natElim x (\ x -> Nat -> Nat) (\ y -> y) (\ x plusx y -> su (plusx y))
-}

mutual

  data _=? {X : Set} : X -> Set where
    [_]=_ : (x y : X) -> x =?
  
  [_]? : forall {X}(x : X){p :  x =?} -> X
  [ x ]?{[ .x ]= y} = y

postulate `plus : Nat -> Nat -> Nat

mkPlus : (x y : Nat) -> `plus x y =?
mkPlus x y = natElim x (\ x -> (y : Nat) -> `plus x y =?)
   (\ y -> [ `plus ze y ]= y)
   (\ x xh y -> [ `plus (su x) y ]= su ([ `plus x y ]?{xh y}))
   y

plus : Nat -> Nat -> Nat
plus x y = [ `plus x y ]?{mkPlus x y}

data _~_ {X : Set}(x : X) : X -> Set where
  r~ : x ~ x

R~ : {X : Set}(x : X) -> x ~ x
R~ x = r~

J : forall {l}{X : Set}{x y : X}(q : x ~ y)
    (P : (y : X)(q : x ~ y) -> Set l)
    (px : P x r~)
    ->
    P y q
J r~ P px = px

_~$~_ : {S T : Set}
  {f g : S -> T} -> f ~ g ->
  {x y : S} -> x ~ y ->
  f x ~ g y
_~$~_ {S}{T}{f}{g} fg {x}{y} xy = J fg (\ g q -> {x y : _} -> x ~ y -> f x ~ g y)
  (\ {x}{y} xy -> J xy (\ y q -> f x ~ f y) r~)
  xy

asso : (x y z : Nat) -> plus (plus x y) z ~ plus x (plus y z)
asso x y z = natElim x (\ x -> (y z : Nat) -> plus (plus x y) z ~ plus x (plus y z))
    (\ y z -> r~)
    (\ x xh y z -> R~ su ~$~ xh y z)
    y z

record One {l} : Set l where constructor <>
record _><_ {l}(S : Set l)(T : S -> Set l) : Set l where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_
infixr 10 _,_

TEL : Nat -> Set1
TEL n = natElim n (\ _ -> Set1)
  One
  \ n H -> Set >< \ X -> X -> H

EL : forall n -> TEL n -> Set
EL n = natElim n (\ n -> TEL n -> Set)
  (\ <> -> One)
  \ n nH (X , T) -> X >< \ x -> nH (T x)

TELQ : forall n -> (T : TEL n)(as bs : EL n T) -> Set
TELQ n = natElim n (\ n -> (T : TEL n)(as bs : EL n T) -> Set)
  (\ <> <> <> -> One)
  \ n nH (X , T) (a , as) (b , bs) ->
    (a ~ b) >< \ q -> nH (T a) as
      (J q (\ b q -> EL n (T b) -> EL n (T a)) (\ bs -> bs) bs)

data Tel : Nat -> Set1 where
  []   : Tel ze
  _,-_ : forall {n}(X : Set)(T : X -> Tel n) -> Tel (su n)
El : forall {n} -> Tel n -> Set
El []       = One
El (X ,- T) = X >< \ x -> El (T x)

TelQ : forall {n}(T : Tel n) -> El T -> El T -> Set
TelQ [] <> <> = One
TelQ (X ,- T) (a , as) (b , bs) = (a ~ b) >< \ q -> TelQ (T b) (J q (\ a q -> El (T a)) as) bs

NoConfNat : (n m : Nat)(G : (n ~ m) -> Set) -> Set
NoConfNat  ze     ze    G = G r~
NoConfNat  ze    (su m) G = One
NoConfNat (su n)  ze    G = One
NoConfNat (su n) (su m) G = (q : n ~ m) -> G (R~ su ~$~ q)
noConfNat : {n m : Nat}(q : n ~ m)(G : (n ~ m) -> Set) -> NoConfNat n m G -> G q
noConfNat {n} q G h = J q (\ m q -> (G : (n ~ m) -> Set) -> NoConfNat n m G -> G q)
  (natElim n (\ n -> (G : n ~ n -> Set) -> NoConfNat n n G -> G r~)
    (\ G h -> h)
    (\ k kh G h -> h r~) )
  G h

data Vec (X : Set) : Nat -> Set where
  [] : Vec X ze
  _,-_ : forall {n} -> X -> Vec X n -> Vec X (su n)
infixr 20 _,-_

vecElim : forall {l}{X : Set}{n : Nat}(xs : Vec X n)
          (P : (n : Nat) -> Vec X n -> Set l)
          (z : P ze [])
          (s : {n : Nat}(x : X)(xs : Vec X n) -> P n xs -> P (su n) (x ,- xs))
          ->
          P n xs
vecElim [] P z s = z
vecElim (x ,- xs) P z s = s x xs (vecElim xs P z s)

vtail : {Y : Set}{m : Nat}(ys : Vec Y (su m)) -> Vec Y m
vtail {Y}{m} ys = vecElim ys
  (\ n xs -> {m : Nat}(ys : Vec Y (su m))
     -> TELQ 2 (Nat , \ n -> Vec Y n , \ _ -> <>) (su m , ys , <>) (n , xs , <>)
     -> Vec Y m)
  (\ {m} ys (q0 , q1 , <>) ->
    noConfNat q0 (\ _ -> Vec Y m) <>)
  (\ {n} x xs h {m} ys (q0 , q1 , <>) -> 
    noConfNat q0 (\ q0 -> ys ~
           fst
           (J q0
            (λ b q →
               EL 1 (Vec Y b , (λ _ → <>)) → EL 1 (Vec Y (su m) , (λ _ → <>)))
            (λ bs → bs) (x ,- xs , <>))
            -> Vec Y m)
       (\ q2 -> J q2 (\ n q2 -> (xs : Vec Y n) ->
          ys ~
      fst
      (J (R~ su ~$~ q2)
       (λ b q →
          EL 1 (Vec Y b , (λ _ → <>)) → EL 1 (Vec Y (su m) , (λ _ → <>)))
       (λ bs → bs) (x ,- xs , <>)) →
      Vec Y m)
      (\ xs _ -> xs)
      xs)
       q1 )
  ys (r~ , r~ , <>)

trichotomy : (n m : Nat)
  (P : Nat -> Nat -> Set)
  (lt : (n m : Nat) -> P n (plus n (su m)))
  (eq : (n : Nat) -> P n n)
  (gt : (n m : Nat) -> P (plus n (su m)) n)
  ->
  P n m
trichotomy = \ n -> natElim n (\ n -> (m : Nat)
  (P : Nat -> Nat -> Set)
  (lt : (n m : Nat) -> P n (plus n (su m)))
  (eq : (n : Nat) -> P n n)
  (gt : (n m : Nat) -> P (plus n (su m)) n)
  ->
  P n m)
  (\ m -> natElim m (\ m ->  (P : Nat → Nat → Set) →
      ((n₂ m₁ : Nat) → P n₂ (plus n₂ (su m₁))) →
      ((n₂ : Nat) → P n₂ n₂) →
      ((n₂ m₁ : Nat) → P (plus n₂ (su m₁)) n₂) → P ze m)
      (\ P lt eq gt -> eq ze)
      \ m h P lt eq gt -> lt ze m)
  \ n nh m -> natElim m (\ m -> (P : Nat → Nat → Set) →
    ((n₁ m₁ : Nat) → P n₁ (plus n₁ (su m₁))) →
    ((n₁ : Nat) → P n₁ n₁) →
    ((n₁ m₁ : Nat) → P (plus n₁ (su m₁)) n₁) → P (su n) m
    )
    (\ P lt eq gt -> gt ze n)
    \ m mh P lt eq gt -> nh m (\ n m -> P (su n) (su m))
      (\ n m -> lt (su n) m)
      (\ n -> eq (su n))
      (\ n m -> gt (su n) m)

natPlusRec : (n : Nat)
  (P : Nat -> Set)
  (h : (n : Nat)(p : (x y : Nat) -> n ~ su (plus x y) -> P y) -> P n)
  ->
  P n
natPlusRec n P h = h n (natElim n (\ n -> (x y : Nat) → n ~ su (plus x y) → P y)
  (\ x y q -> noConfNat q (\ _ -> P y) <>)
  \ n nh x -> natCase x (\ x -> (y : Nat) → su n ~ su (plus x y) → P y)
    (\ y q -> noConfNat q (\ _ -> P y) \ q' -> J q' (\ y _ -> P y) (h n nh))
    \ x y q -> noConfNat q (\ _ -> P y) \ q' -> nh x y q')

postulate gcd' : Nat -> Nat -> Nat
mkGcd : (x y : Nat) -> gcd' x y =?
mkGcd x y = natPlusRec x (\ x -> (y : Nat) -> gcd' x y =?)
  (\ x xh y -> natPlusRec y (\ y -> gcd' x y =?)
    \ y yh -> natCase x (\ x ->
       ((x₂ y₃ : Nat) →
         x ~ su (plus x₂ y₃) → (y₄ : Nat) → gcd' y₃ y₄ =?) ->
         ((x₂ y₃ : Nat) → y ~ su (plus x₂ y₃) → gcd' x y₃ =?) ->
         gcd' x y =?)
         (\ xh yh -> [ gcd' ze y ]= y)
         (\ x xh yh -> natCase y (\ y -> ((x₂ y₃ : Nat) → y ~ su (plus x₂ y₃) → gcd' (su x) y₃ =?)
             -> gcd' (su x) y =?)
             (\ yh -> [ gcd' (su x) ze ]= su x)
             (\ y yh -> trichotomy x y (\ x y ->
               ((x₂ y₃ : Nat) →
           su x ~ su (plus x₂ y₃) → (y₄ : Nat) → gcd' y₃ y₄ =?) ->
               ((x₂ y₃ : Nat) →
           su y ~ su (plus x₂ y₃) → gcd' (su x) y₃ =?) ->
               gcd' (su x) (su y) =?)
               (\ n m xh yh -> [ gcd' (su n) (su (plus n (su m))) ]=
                          [ gcd' (su n) (su m) ]?{yh n (su m) r~})
               (\ n xh yh -> [ gcd' (su n) (su n) ]= su n)
               (\ n m xh yh -> [ gcd' (su (plus n (su m))) (su n) ]=
                               [ gcd' (su m) (su n) ]?{xh n (su m) r~ (su n)})
               xh yh)
             yh)
         xh yh)
  y

gcd : Nat -> Nat -> Nat
gcd x y = [ gcd' x y ]?{mkGcd x y}

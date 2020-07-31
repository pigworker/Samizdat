module IIIR where

open import Agda.Primitive

id : forall {l}{X : Set l} -> X -> X
id x = x

_-_ : forall {j k l}
      {A : Set j}{B : A -> Set k}{C : (a : A) -> B a -> Set l}
      (f : {a : A}(b : B a) -> C a b) ->
      (g : (a : A) -> B a)
      (a : A) -> C a (g a)
(f - g) a = f (g a)
infixl 3 _-_

module UPOLY {l} where

  data Zero : Set l where

  record One : Set l where constructor <>

  record Sg (S : Set l)(T : S -> Set l) : Set l where
    constructor _,_
    field
      fst : S
      snd : T fst
  open Sg public
  infixr 4 _,_

  record Up (X : Set l) : Set (lsuc l) where
    constructor up
    field
      down : X
  open Up public

  record Fam (X : Set (lsuc l)): Set (lsuc l) where
    constructor _/_
    field
      Rep     : Set l
      meaning : Rep -> X
  open Fam public

  data _==_ {X : Set l}(x : X) : X -> Set l where
    refl : x == x -- boo, hiss

open UPOLY

{-# BUILTIN EQUALITY _==_ #-}

cong : forall {k l}{S : Set k}{T : Set l}(f : S -> T){s s' : S} -> s == s' -> f s == f s'
cong f refl = refl

postulate
  ext : forall {k l}{S : Set k}{T : S -> Set l}{f g : (s : S) -> T s} ->
         ((s : S) -> f s == g s) -> f == g


module FAMKIT {l} where

  KON : (A : Set l) -> Fam (Up A)
  KON A = A / up

  SG : {X : Set (lsuc l)}{Y : X -> Set (lsuc l)} ->
       (B : Fam X)(C : (x : X) -> Fam (Y x)) ->
       Fam (Sg X Y)
  Rep     (SG (S / f) C) = Sg S (Rep - C - f)
  meaning (SG (S / f) C) (s , t) = let x = f s in x , meaning (C x) t

  PI : (A : Set l)
       {Y : A -> Set (lsuc l)}(C : (a : A) -> Fam (Y a)) ->
       Fam ((a : A) -> Y a)
  Rep     (PI A C) = (a : A) -> Rep (C a)
  meaning (PI A C) f a = meaning (C a) (f a)
       

open FAMKIT

module IIR {l}(I : Set l)(J : I -> Set (lsuc l)) where

  data Code : Set (lsuc l)
  AtLeast : Code -> Set (lsuc l)

  data Code where
    var : (i : I) -> Code
    kon : (A : Set l) -> Code
    sg  : (B : Code)(C : AtLeast B -> Code) -> Code
    pi  : (A : Set l)(C : A -> Code) -> Code

  AtLeast (var i)  = J i
  AtLeast (kon A)  = Up A
  AtLeast (sg B C) = Sg (AtLeast B) \ b -> AtLeast (C b)
  AtLeast (pi A C) = (a : A) -> AtLeast (C a)

  module KNOT (F : I -> Code)
              (f : (i : I) -> AtLeast (F i) -> J i)
              where

    data Mu (i : I) : Set l
    Node : (C : Code) -> Set l
    atLeast : (C : Code) -> Node C -> AtLeast C
    decode : forall {i} -> Mu i -> J i
    data Mu i where
      [_] : Node (F i) -> Mu i
    decode {i} [ n ] = f i (atLeast (F i) n)
    Node (var i) = Mu i
    Node (kon A) = A
    Node (sg B C) = Sg (Node B) \ b -> Node (C (atLeast B b))
    Node (pi A C) = (a : A) -> Node (C a)
    atLeast (var i) n = decode n
    atLeast (kon A) a = up a
    atLeast (sg B C) (b , c) = atLeast B b , atLeast (C (atLeast B b)) c
    atLeast (pi A C) g a = atLeast (C a) (g a)

    MU : (i : I) -> Fam (J i)
    MU i = Mu i / decode

  open KNOT public

open IIR public

data TyTag : Set where baseT arrT : TyTag

Ty : Set
Ty = Mu One (\ _ -> One) (\ _ -> sg (kon TyTag) \ {
    (up baseT) -> kon One ;
    (up arrT) -> sg (var <>) \ _ -> var <>})
  _ <>

pattern base     = [ baseT , <> ]
pattern _>>_ S T = [ arrT , S , T ]

data BwdTag : Set where nilT snocT : BwdTag

Bwd : Set -> Set
Bwd X = Mu One (\ _ -> One) (\ _ -> sg (kon BwdTag) \ {
    (up nilT) -> kon One ;
    (up snocT) -> sg (var <>) \ _ -> kon X })
  _ <>

pattern []        = [ nilT , <> ]
pattern _-,_ xz x = [ snocT , xz , x ]

data IxTag : Set where zeT suT : IxTag

IX : {X : Set} -> Bwd X -> Fam (Up X)
IX {X} = MU (Bwd X) (\ _ -> Up X)
  (\ {
    []       -> kon Zero ;
    (xz -, x) -> sg (kon IxTag) \ { (up zeT) -> kon One ; (up suT) -> var xz } })
  \ { [] (up ())
    ; (xz -, x) (up zeT , _) -> up x
    ; (xz -, S) (up suT , i) -> i
    }

Ix : {X : Set} -> Bwd X -> Set
Ix G = Rep (IX G)
proj : {X : Set}(G : Bwd X) -> Ix G -> X
proj G = down - meaning (IX G)

data Dir : Set where syn chk : Dir

TmIn : Set
TmIn = Sg (Bwd Ty) \ G ->
       Sg Dir \ {
         syn -> One ;
         chk -> Ty }

TmOut : TmIn -> Set1
TmOut (G , syn , <>) = Up Ty
TmOut (G , chk , T)  = One

data SynTag : Set where va ap ty : SynTag

IsArr : Ty -> Set
IsArr base = Zero
IsArr (S >> T) = One

isArr : forall {l}(R : Ty)(Rarr : IsArr R) -> {P : Ty -> Set l} ->
          ((S T : Ty) -> P (S >> T)) -> P R
isArr base () p
isArr (S >> T) Rarr p = p S T

data ChkTag (T : Ty) : Set where
  emb : ChkTag T
  lam : IsArr T -> ChkTag T

TERM : (i : TmIn) -> Fam (TmOut i)
TERM = MU TmIn TmOut
        (\ { (G , syn , <>) -> sg (kon SynTag) \ {
               (up va) -> kon (Ix G) ;
               (up ap) -> sg (var (G , syn , <>)) \ {
                 (up base)     -> kon Zero ;
                 (up (S >> T)) -> var (G , chk , S) } ;
               (up ty) -> sg (kon Ty) \ { (up T) -> var (G , chk , T)} } ;
             (G , chk , T) -> sg (kon (ChkTag T)) \ {
               (up emb) -> sg (var (G , syn , <>)) \ { (up S) -> kon (S == T) } ;
               (up (lam Tarr)) -> isArr T Tarr \ S T -> var ((G -, S) , chk , T)} })
        \ { (G , syn , <>) (up va , up i) -> up (proj G i)
          ; (G , syn , <>) (up ap , up base , up ())
          ; (G , syn , <>) (up ap , up (S >> T) , <>) -> up T
          ; (G , syn , <>) (up ty , up T , _) -> up T
          ; (G , chk , T) n -> _
          }

Graph : forall {l}(I : Set l)(J : I -> Set (lsuc l)) ->
          Code I J -> Code (Sg (Up I) (J - down)) \ _ -> One
phaph : forall {l}(I : Set l)(J : I -> Set (lsuc l)) ->
          (C : Code I J) -> AtLeast _ _ (Graph I J C) -> AtLeast I J C
Graph I J (var i) = sg (kon (J i)) \ { (up j) -> var (up i , j) }
Graph I J (kon A) = kon (Up A)
Graph I J (sg B C) = sg (Graph I J B) \ { b -> Graph I J (C (phaph I J B b)) }
Graph I J (pi A C) = pi (Up A) \ {(up a) -> Graph I J (C a) }
phaph I J (var i) (up j , _) = j
phaph I J (kon A) (up (up a)) = up a
phaph I J (sg B C) (b , c) = let x = phaph I J B b in x , phaph I J (C x) c
phaph I J (pi A C) f a = phaph I J (C a) (f (up a))

MuG : forall {l}{I : Set l}{J : I -> Set (lsuc l)}
        (F : I -> Code I J)(f : (i : I) -> AtLeast I J (F i) -> J i) ->
        (Sg (Up I) (J - down)) -> Code (Sg (Up I) (J - down)) \ _ -> One
MuG {l}{I}{J} F f (up i , j) = sg (Graph I J (F i)) \ n -> kon (f i (phaph I J (F i) n) == j)

mkMuG : forall {l}{I : Set l}{J : I -> Set (lsuc l)}
        {F : I -> Code I J}{f : (i : I) -> AtLeast I J (F i) -> J i} ->
        {i : I} -> (x : Mu I J F f i) -> Mu _ _ (MuG F f) _ (up i , decode _ _ _ _ x)
mkMuGn : forall {l}{I : Set l}{J : I -> Set (lsuc l)}
         {F : I -> Code I J}{f : (i : I) -> AtLeast I J (F i) -> J i} ->
         (C : Code I J) -> (x : Node I J F f C) -> Sg (Node _ _ (MuG F f) _ (Graph I J C)) \ x' ->
         phaph I J C (atLeast (Sg (Up I) (\ a -> J (down a))) (λ _ → One) (MuG F f) _ (Graph I J C) x') == atLeast I J F f C x
  
mkMuG {F = F}{f = f}{i = i} [ x ] with mkMuGn (F i) x
... | y , q = [ y , cong (f i) q ]

mkMuGn (var i) x = (_ , mkMuG x) , refl
mkMuGn (kon A) a = (up a , refl)
mkMuGn (sg B C) (b , c) with mkMuGn B b
... | b' , q with mkMuGn (C _) c
... | c' , q' with atLeast _ _ _ _ B b | atLeast _ _ _ _ (C _) c
mkMuGn (sg B C) (b , c) | b' , refl | c' , refl | ._ | ._ = (b' , c') , refl
fst (mkMuGn (pi A C) g) (up a) = fst (mkMuGn (C a) (g a))
snd (mkMuGn (pi A C) g) = ext \ a -> snd (mkMuGn (C a) (g a))


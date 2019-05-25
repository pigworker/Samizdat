module IC where

data Zero : Set where

record One : Set where constructor <>

record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg
_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T
infixr 4 _,_ _*_

unc : forall {l}{S T}{P : Sg S T -> Set l} ->
      ((s : S)(t : T s) -> P (s , t)) ->
      (x : Sg S T) -> P x
unc p (s , t) = p s t

data _==_ {X : Set}(x : X) : X -> Set where
  refl : x == x

record IK (I : Set) : Set1 where
  constructor _<|_
  field
    Cmd : Set
    Rsp : Cmd -> I -> Set
open IK

_|>_ : Set -> Set -> Set1
I |> O = O -> IK I

[_] : forall {I O} -> I |> O -> (I -> Set) -> (O -> Set)
[ F ] X o = Sg (Cmd (F o)) \ c -> forall i -> Rsp (F o) c i -> X i

fun : forall {I O}(F : I |> O){X Y : I -> Set} ->
  ((i : I) -> X i -> Y i) ->
   (o : O) -> [ F ] X o -> [ F ] Y o
fun F f o (c , k) = c , \ i r -> f i (k i r)

data _+_ (S T : Set) : Set where
  inl : S -> S + T
  inr : T -> S + T

_<+>_ : forall {l}{S T : Set}{P : S + T -> Set l} ->
        ((s : S) -> P (inl s)) ->
        ((t : T) -> P (inr t)) ->
        (x : S + T) -> P x
(f <+> g) (inl s) = f s
(f <+> g) (inr t) = g t

_+C_ : forall {I O} -> (F G : I |> O) -> I |> O
Cmd ((F +C G) o) = Cmd (F o) + Cmd (G o)
Rsp ((F +C G) o) (inl c) i = Rsp (F o) c i
Rsp ((F +C G) o) (inr c) i = Rsp (G o) c i

inlC : forall {I O}{F G : I |> O}{X} o ->
       [ F ] X o -> [ F +C G ] X o
inlC o (c , k) = inl c , k

inrC : forall {I O}{F G : I |> O}{X} o ->
       [ G ] X o -> [ F +C G ] X o
inrC o (c , k) = inr c , k

caseC : forall {l}{I O}{F G : I |> O}{X}{P : Set l} o ->
        ([ F ] X o -> P) ->
        ([ G ] X o -> P) ->
        [ F +C G ] X o -> P
caseC o f g (inl c , k) = f (c , k)
caseC o f g (inr c , k) = g (c , k)

_*C_ : forall {I O} -> (F G : I |> O) -> I |> O
Cmd ((F *C G) o) = Cmd (F o) * Cmd (G o)
Rsp ((F *C G) o) (c , c') i = Rsp (F o) c i + Rsp (G o) c' i

pairC : forall {I O}{F G : I |> O}{X} o ->
       [ F ] X o -> [ G ] X o -> [ F *C G ] X o
pairC o (c , k) (c' , k') = ((c , c') , \ i -> k i <+> k' i)

riapC : forall {l}{I O}{F G : I |> O}{X}{P : Set l} o ->
       ([ F ] X o -> [ G ] X o -> P) -> [ F *C G ] X o -> P
riapC o p ((c , c') , k) = p
  (c , (\ i r -> k i (inl r)))
  (c' , (\ i r -> k i (inr r)))

_-C_ : forall {I J K} -> I |> J -> J |> K -> I |> K
Cmd ((F -C G) k) =
  Sg (Cmd (G k)) \ gc -> forall {j} ->
  Rsp (G k) gc j ->
  Cmd (F j)
Rsp ((F -C G) k) (gc , fc) i =
  Sg _ \ j ->
  Sg (Rsp (G k) gc j) \ gr ->
  Rsp (F j) (fc gr) i

toC : forall {I J K}(F : I |> J)(G : J |> K)(X : I -> Set)(k : K) ->
  [ G ] ([ F ] X) k -> [ F -C G ] X k
toC F G X k (gc , gk) =
  (gc , (\ gr -> fst (gk _ gr))) ,
  \ { i (j , gr , fr) -> let fc , fk = gk j gr in fk i fr }

fromC : forall {I J K}{P : Set}(F : I |> J)(G : J |> K)(X : I -> Set)(k : K) ->
  ([ G ] ([ F ] X) k -> P) -> ([ F -C G ] X k -> P)
fromC F G X k p ((gc , gk) , ck) = p (gc , \ j gr -> gk gr , \ i fr -> ck i (j , gr , fr))


IM : forall {I O} -> (O -> I) -> I |> O
Cmd (IM f o) = One
Rsp (IM f o) <> i = f o == i

pack : forall {I O}{X}{f : O -> I} o ->
  X (f o) -> [ IM f ] X o
pack o x = <> , \ { _ refl -> x }

unpack : forall {l}{I O}{X}{f : O -> I}{P : Set l} o ->
  (X (f o) -> P) -> [ IM f ] X o -> P
unpack o p (<> , k) = p (k _ refl)

Pi : forall {I O}(A : Set)(F : A -> I |> O) -> I |> O
Cmd (Pi A F o) = (a : A) -> Cmd (F a o)
Rsp (Pi A F o) f i = Sg A \ a -> Rsp (F a o) (f a) i

apC : forall {I O}{A : Set}{F : A -> I |> O}{X} o ->
  [ Pi A F ] X o -> (a : A) -> [ F a ] X o
apC o (c , f) a = c a , \ i r -> f i (a , r) 

KO : forall {I O} -> (A : O -> Set) -> I |> O
Cmd (KO A o) = A o
Rsp (KO A o) _ _ = Zero

koC : forall {I O}{A : O -> Set}{B : I -> Set} (o : O)(a : A o) -> [ KO A ] B o
koC o a = a , \ _ ()

module _ {I O : Set}(F : (I + O) |> O) where

  FF : (I -> Set) -> (O -> Set) -> (O -> Set)
  FF X Y = [ F ] (X <+> Y)

  data Mu (o : O) : Set where
    go : (c : Cmd (F o)) ->
         ((o' : O)(r : Rsp (F o) c (inr o')) -> Mu o') ->
         Mu o

  MU : I |> O
  Cmd (MU o) = Mu o
  Rsp (MU o) (go c k) j =
    Sg (I + O) \
    { (inl i) -> i == j * Rsp (F o) c (inl i)
    ; (inr o') -> 
        Sg (Rsp (F o) c (inr o')) \ r ->
        Rsp (MU o') (k o' r) j
    }

  inn : forall {X} (o : O) -> [ F ] (X <+> [ MU ] X) o -> [ MU ] X o
  inn {X} o (c , k) =
    (go c (\ o' r -> fst (k (inr o') r))) ,
    \ i -> unc ((\ { _ (refl , r) -> k (inl i) r } )
            <+> \ o' -> unc \ r rs -> snd (k (inr o') r) _ rs) 

  module _ (X : I -> Set)(Y : O -> Set)
    (g : (o : O) -> FF X Y o -> Y o)

    where

    iter : (o : O) -> [ MU ] X o -> Y o
    iter' : (o : O)
            (t : Mu o) ->
            (k : (i : I) -> Rsp (MU o) t i -> X i) ->
            Y o

    iter o (t , k) = iter' o t k 
    iter' o (go c t) k
      = g o (c , (    (\ i r -> k i (inl i , refl , r))
                  <+> \ o' r -> iter' o' (t o' r) \ i rs -> k i (inr o' , r , rs)))

  record Nu (o : O) : Set
  Go : (o : O) -> Set
  Go o =
    Sg (Cmd (F o)) \ c ->
    (o' : O)(r : Rsp (F o) c (inr o')) -> Nu o'

  record Nu o where
    coinductive
    field
      force : Go o
  open Nu

  data Tr {o : O}(p : Nu o)(i : I) : Set
  Tr' : forall {o : O} -> Go o -> I -> Set
  data Tr {o} p i where
    stop : Rsp (F o) (fst (force p)) (inl i) -> Tr p i
    <_> : Tr' (force p) i -> Tr p i
  Tr' {o} (c , k) j =
    Sg _ \ o' -> Sg (Rsp (F o) c (inr o')) \ r ->
    Tr (k o' r) j

  NU : I |> O
  Cmd (NU o) = Nu o
  Rsp (NU o) p i = Tr p i

  out : forall {l}{X}{P : Set l} o ->
    ([ F ] (X <+> [ NU ] X) o -> P) -> [ NU ] X o -> P
  out o m (p , k) =
    let (c , f) = force p in m (c ,
    (
      (\ i r -> k i (stop r))
    <+>
      \ o' r -> f o' r , \ i ts -> k i < o' , r , ts >
    ))

  module _ (X : I -> Set)(Y : O -> Set)
    (g : (o : O) -> Y o -> FF X Y o)

    where

    coiter : (o : O) -> Y o -> [ NU ] X o
    force (fst (coiter o y)) with g o y
    ... | c , k = c , \ o' r -> fst (coiter o' (k (inr o') r))
    snd (coiter o y) i (stop r) with g o y
    ... | c , k = k (inl i) r
    snd (coiter o y) i < o' , r , t > with g o y
    ... | c , k = snd (coiter o' (k (inr o') r)) i t

Munch : Set -> ((One + One) + One) |> One
Stage : Set -> (One + One) |> One
Eater : Set -> One |> One
Munch A = (IM (\ _ -> inl (inl <>)) *C IM \ _ -> inl (inr <>))
                +C Pi A \ _ -> IM \ _ -> inr <>
Stage A = MU (Munch A)
Eater A = NU (Stage A)

Stream : One |> One
Stream = NU (IM inl *C IM inr)

eat : forall {A B} -> [ Eater A ] (\ _ -> B) <>
                   -> [ Stream ] (\ _ -> A) <>
                   -> [ Stream ] (\ _ -> B) <>
eat {A}{B} f as = coiter (IM inl *C IM inr) (\ _ -> B)
                   (\ _ -> [ Eater A ] (\ _ -> B) <> * [ Stream ] (\ _ -> A) <>)
                   (\ { _ -> unc (out (Stage A) <> (iter (Munch A) _ _ (
                     \ _ -> caseC <>
                     (riapC <> (unpack <> \ b -> unpack <> \ e as ->
                           pairC <> (pack <> b) (pack <> (e , as))))
                     \ h -> out (IM inl *C IM inr) <>
                             (riapC <>
                               (unpack <> \ a -> unpack <> \ as ->
                                 let _ , j = apC <> h a in j (inr <>) refl as) ) )
                     <>)) })
                   <> (f , as)

always : forall {X} -> X -> Zero |> ([ Stream ] (\ _ -> X) <>)
always x = NU (out (IM inl *C IM inr) <> (riapC <> (unpack <> \ x' -> 
  unpack <> (KO (\ _ -> x == x') *C IM inr))))

data Two : Set where ff tt : Two

ffs : [ Stream ] (\ _ -> Two) <>
ffs = coiter (IM inl *C IM inr) (\ _ -> Two) (\ _ -> One)
      (\ _ _ -> pairC <> (pack <> ff) (pack <> <>)) <> <>

isFfs : [ always ff ] (\ ()) ffs
isFfs = coiter _ (\ ()) (\ i -> i == ffs) (unc
  (\ { ._ ._ refl -> (refl , _) ,
    ((\ ()) <+>
      \ { t (inl ())
        ; ._ (inr refl) -> refl
        }) }))
  ffs refl

NAT : Zero |> One
NAT = MU (KO (\ _ -> One) +C IM inr)

CLIENTB : (Zero + One) |> One
CLIENTB = (((\ ()) -C NAT) +C (IM inr -C Stream))

CLIENT : Zero |> One
CLIENT = MU CLIENTB

SERVER : Zero |> One
SERVER = NAT -C Stream

run : [ CLIENT ] (\ ()) <> ->
      [ SERVER ] (\ ()) <> ->
      [ NAT ] (\ ()) <>
run = iter CLIENTB (\ ())
  (\ _ -> [ SERVER ] (\ ()) <> ->
          [ NAT ] (\ ()) <>)
  (\ _ -> caseC
   _
   (fromC (\ ()) NAT _ <> \ n _ -> iter _ _ _ (
      \ _ -> caseC _ (\ _ -> inn _ <> (inlC <> (<> , \ _ ())) )
                     (\ { (<> , r) -> inn _ <> (inrC <> (<> , \ { _ refl -> r _ refl })) }))
             <> n)
  (fromC (IM inr) Stream _ <> \ rs -> fromC NAT Stream _ <> (out _ <>
    (riapC <> (unpack <> \ n -> unpack <> \ ns -> iter _ _ (\ _ -> _ -> _)
      (\ o -> caseC <>
        (\ _ -> out _ <> (riapC <> (unpack <> (unpack <> \ r _ -> r (toC NAT Stream _ <> ns)))))
        \ { (<> , h) -> out _ <> (riapC <> \ _ -> unpack <> \ rs -> h _ refl rs) }
      ) <> n rs)))))
  <>

myServer : [ NAT ] (\ ()) <> -> [ SERVER ] (\ ()) <>
myServer n = toC NAT Stream _ <> (coiter _ _ ([ NAT ] (λ ()))
  (\ _ n -> pairC <> (pack <> n) (pack <> (inn _ <> (inrC <> (pack <> n)))))
  <> n)

data Nat : Set where
  ze : Nat
  su : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

myClient : Nat -> [ NAT ] (\ ()) <> -> [ CLIENT ] (\ ()) <>
myClient ze     n = inn _ <> (inlC <> (toC (\ ()) NAT _ <> (fun NAT (\ ()) <> n)))
myClient (su m) n = inn _ <> (inrC <> (toC (IM inr) Stream _ <> (
  coiter _ _ ([ NAT ] (λ ())) (\ _ n -> pairC <>
    (pack <> (pack <> (myClient m n)))
    (pack <> (inn _ <> (inrC <> (pack <> n))))
    ) <> n)))

see : [ NAT ] (\ ()) <> -> Nat
see = iter _ _ (\ _ -> Nat) (\ _ -> caseC <> (\ _ -> ze) (unpack <> su)) <>

tryMe : Nat
tryMe = see (run
  (myClient 6 (inn _ <> (inlC <> (<> , \ _ ()))))
  (myServer (inn _ <> (inlC <> (<> , \ _ ())))))

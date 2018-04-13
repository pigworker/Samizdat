module Kipling where

record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg
_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T
infixr 4 _,_ _*_

data Nat : Set where
  ze : Nat
  su : Nat -> Nat

data Dir : Set where chk syn : Dir

data _<=_ : Nat -> Nat -> Set where
  _o' : forall {n m} -> n <= m -> n <= (su m)
  _os : forall {n m} -> n <= m -> (su n) <= (su m)
  oz : ze <= ze

oe : {n : Nat} -> ze <= n
oe {ze} = oz
oe {su x} = oe o'

oi : {n : Nat} -> n <= n
oi {ze} = oz
oi {su x} = oi os

_-o-_ : forall {n m l} -> n <= m -> m <= l -> n <= l
th -o- (ph o') = (th -o- ph) o'
(th o') -o- (ph os) = (th -o- ph) o'
(th os) -o- (ph os) = (th -o- ph) os
oz -o- oz = oz

data Tr : forall {n m l}(th : n <= m)(ph : m <= l)(ps : n <= l) -> Set where
  _t-' : forall {n m l}{th : n <= m}{ph : m <= l}{ps : n <= l} ->
          Tr th ph ps -> Tr th (ph o') (ps o')
  _t's : forall {n m l}{th : n <= m}{ph : m <= l}{ps : n <= l} ->
          Tr th ph ps -> Tr (th o') (ph os) (ps o')
  _tss : forall {n m l}{th : n <= m}{ph : m <= l}{ps : n <= l} ->
          Tr th ph ps -> Tr (th os) (ph os) (ps os)
  tzz : Tr oz oz oz

oTr : forall {n m l}(th : n <= m)(ph : m <= l) -> Tr th ph (th -o- ph)
oTr th (ph o') = oTr th ph t-'
oTr (th o') (ph os) = oTr th ph t's
oTr (th os) (ph os) = oTr th ph tss
oTr oz oz = tzz

_-oo-_ : forall {p n m l}
         {th : p <= n}{ph : n <= m}{ps : p <= m}{xi : m <= l}{ch : p <= l} ->
         Tr th ph ps -> Tr ps xi ch ->
         Sg (n <= l) \ om -> Tr ph xi om * Tr th om ch
tr0 -oo- (tr1 t-') with tr0 -oo- tr1
... | om , ur0 , ur1 = (om o') , (ur0 t-') , (ur1 t-')
(tr0 t-') -oo- (tr1 t's) with tr0 -oo- tr1
... | om , ur0 , ur1 = (om o') , (ur0 t's) , (ur1 t-')
(tr0 t's) -oo- (tr1 t's) with tr0 -oo- tr1
... | om , ur0 , ur1 = (om os) , (ur0 tss) , (ur1 t's)
(tr0 tss) -oo- (tr1 tss) with tr0 -oo- tr1
... | om , ur0 , ur1 = (om os) , (ur0 tss) , (ur1 tss)
tzz -oo- tzz = oz , tzz , tzz

_-oi : forall {n m}(th : n <= m) -> Tr th oi th
(th o') -oi = (th -oi) t's
(th os) -oi = (th -oi) tss
oz -oi = tzz

data Tm (n : Nat) : Dir -> Set where
  Pi  : (S : Tm n chk)(T : Tm (su n) chk) -> Tm n chk
  la  : (t : Tm (su n) chk) -> Tm n chk
  _$_ : (f : Tm n syn)(s : Tm n chk) -> Tm n syn
  Tw tt ff  : Tm n chk
  If  : (e : Tm n syn)(T F : Tm n chk) -> Tm n syn
  if  : (P : Tm (su n) chk)(e : Tm n syn)(t f : Tm n chk) -> Tm n syn
  va  : su ze <= n -> Tm n syn
  [_] : Tm n syn -> Tm n chk
  _::_ : Tm n chk -> Tm n chk -> Tm n syn

data Nm (n : Nat) : Dir -> Set where
  Pi  : (S : Nm n chk)(T : Nm (su n) chk) -> Nm n chk
  la  : (t : Nm (su n) chk) -> Nm n chk
  _$_ : (f : Nm n syn)(s : Nm n chk) -> Nm n syn
  Tw tt ff : Nm n chk
  If  : (e : Nm n syn)(T F : Nm n chk) -> Nm n syn
  if  : (P : Nm (su n) chk)(e : Nm n syn)(t f : Nm n chk) -> Nm n syn
  va  : su ze <= n -> Nm n syn
  [_] : Nm n syn -> Nm n chk

infixl 4 _$_

thinNm : forall {n m d} -> Nm n d -> n <= m -> Nm m d
thinNm (Pi S T) th = Pi (thinNm S th) (thinNm T (th os))
thinNm (la t) th = la (thinNm t (th os))
thinNm (f $ s) th = thinNm f th $ thinNm s th
thinNm Tw th = Tw
thinNm tt th = tt
thinNm ff th = ff
thinNm (If e T F) th = If (thinNm e th) (thinNm T th) (thinNm F th)
thinNm (if P e t f) th = if (thinNm P (th os)) (thinNm e th) (thinNm t th) (thinNm f th)
thinNm (va x) th = va (x -o- th)
thinNm [ e ] th = [ thinNm e th ]

data Two : Set where tt ff : Two

record One : Set where constructor <>

data Zero : Set where

data _+_ (S T : Set) : Set where
  inl : S -> S + T
  inr : T -> S + T

data Eek : Set where
  eekSubTy eekstop eekStop eekCodomain : Eek -> Eek
  eekSubTyMismatch eekIfUnBool eekNotTy chkVCatch chkV[] eekAppNoFun eekifUnBool eeksynCCatch : Eek
  
  

data Maybe (X : Set) : Set where
  yes : X -> Maybe X
  no  : Eek -> Maybe X

_>>=_ : {S T : Set} -> Maybe S -> (S -> Maybe T) -> Maybe T
no e >>= k = no e
yes s >>= k = k s

mutual

  data U (n : Nat) : Set where
    [_]  : Nm n syn -> U n
    Two' : U n
    Pi' : (S : U n)(T : {m : Nat}(th : n <= m) -> Va th S -> Maybe (U m)) -> U n

  Va : {n m : Nat} -> n <= m -> U n -> Set
  Vm : {n : Nat} -> Maybe (U n) -> Set
  Go : {n m : Nat} -> n <= m -> U n -> Set
  Va {n}{m} th T = Nm m syn + Go th T
  Go th [ _ ]      = Zero
  Go th Two'       = Two
  Go th (Pi' S T)  = forall {l}{ph : _ <= l}{ps : _ <= l} -> Tr th ph ps ->
                     (s : Va ps S) -> Vm (T ps s)
  Vm (no _) = One
  Vm (yes T) = Maybe (Va oi T)

thVa : forall {n m m'}(th : n <= m)(T : U n) -> Va th T -> {ph : m <= m'}{ps : n <= m'} -> Tr th ph ps -> Va ps T
thVa th T (inl n) {ph = ph} _ = inl (thinNm n ph)
thVa th [ x ] (inr ()) _
thVa th Two' (inr b) _ = inr b
thVa th (Pi' S T) (inr g) tr0 = inr \ tr1 s -> let _ , ur0 , ur1 = tr0 -oo- tr1 in g ur1 s

Cell : Nat -> Set
Cell m = Sg Nat \ l -> Sg (l <= m) \ th -> Sg (U l) \ X -> Va th X

thCell : forall {m m'} -> Cell m -> m <= m' -> Cell m'
thCell (l , th , T , t) ph = l , (th -o- ph) , T , thVa th T t (oTr th ph)

Env : Nat -> Nat -> Set
Env n m = su ze <= n -> Cell m

snoc : forall {n m} -> Env n m -> Cell m -> Env (su n) m
snoc g c (x o') = g x
snoc g c (x os) = c

thEnv : forall {n m m'} -> Env n m -> m <= m' -> Env n m'
thEnv ga ph x with ga x
... | l , th , T , t = l , (th -o- ph) , T , thVa th T t (oTr th ph)


mutual

  Stop : forall {n} -> U n -> Maybe (Nm n chk)
  Stop [ T ] = yes [ T ]
  Stop Two' = yes Tw
  Stop (Pi' S' T') = Stop S' >>= \ S -> StopM S (T' (oi o') (inl (va (oe os))))

  StopM : forall {n} -> Nm n chk -> Maybe (U (su n)) -> Maybe (Nm n chk)
  StopM S (yes T') = Stop T' >>= \ T -> yes (Pi S T)
  StopM S (no e) = no (eekStop e)

  stop : forall {n m}(T : U n)(th : n <= m)(v : Va th T) -> Maybe (Nm m chk)
  stop T th (inl e) = yes [ e ]
  stop [ _ ] th (inr ())
  stop Two' th (inr tt) = yes tt
  stop Two' th (inr ff) = yes ff
  stop (Pi' S T) th (inr f) = stopM (T (th o') (inl (va (oe os)))) (f ((th -oi) t-') (inl (va (oe os))))

  stopM : forall {m} (W : Maybe (U (su m))) -> Vm W -> Maybe (Nm m chk)
  stopM (yes W) (yes w) = stop W oi w >>= \ t -> yes (la t)
  stopM (yes W) (no e) = no (eekstop e)
  stopM (no e) _ = no (eekstop e)

subTy : forall {l n m}(th : l <= m)(ph : n <= m)(S : U l)(T : U n) -> Va th S -> Maybe (Va ph T)
subTy th ph S T (inl x) = yes (inl x)
subTy th ph [ _ ] _ (inr ())
subTy th ph Two' Two' (inr x) = yes (inr x)
subTy th ph (Pi' S T) (Pi' S' T') (inr f) = yes (inr (\ {p}{ph'}{ps'} tr s' ->
  help th ph S S' T (T' ps' s') f ph' ps' tr (subTy ps' (th -o- ph') S' S s') s'
  ))
  where
  help : forall {l n m p}
         (th : l <= m) (ph : n <= m) (S : U l) (S' : U n)
         (T  : forall {m'} (th' : l <= m') -> Va th' S -> Maybe (U m'))
         (Ts : Maybe (U p))
         (f : forall {p'} {ph' : m <= p'} {ps' : l <= p'} ->
           Tr th ph' ps' -> (s : Va ps' S) -> Vm (T ps' s)) ->
         (ph' : m <= p) (ps' : n <= p) -> Tr ph ph' ps' ->
         Maybe (Va (th -o- ph') S) -> (s' : Va ps' S') -> Vm Ts
  help th ph S S' T (yes T's') f ph' ps' tri (yes s) s' = welp (T (th -o- ph') s) (f (oTr th ph') s)
    where
    welp : (W : Maybe (U _)) -> Vm W -> Maybe (Va oi T's')
    welp (yes Ts) (yes fs) = subTy oi oi Ts T's' fs
    welp (yes _) (no e) = no (eekSubTy e)
    welp (no e) _ = no (eekSubTy e)
 
  help th ph S S' T (yes _) f ph' ps' tri (no e) s' = no e
  help th ph S S' T (no e) f ph' ps' tri ms s' = <>

subTy _ _ _ _ _ = no eekSubTyMismatch

mutual

  Ty : forall {n m d} -> Env n m -> Tm n d -> Maybe (U m)
  Ty g (Pi S T)    = Ty g S >>= \ S' -> yes (Pi' S' \ th s' -> Ty (snoc (thEnv g th) (_ , th , S' , s')) T)
  Ty g Tw          = yes Two'
  Ty g (If e T F)  with synC g e
  Ty g (If e T F) | yes (_ , _ , Two' , inl b)  =
    Ty g T >>= \ T' -> Stop T' >>= \ T ->
    Ty g F >>= \ F' -> Stop F' >>= \ F ->
    yes [ If b T F ]
  Ty g (If e T F) | yes (_ , _ , Two' , inr tt) = Ty g T
  Ty g (If e T F) | yes (_ , _ , Two' , inr ff) = Ty g F
  Ty g (If e T F) | yes (_ , _ , _ , _) = no eekIfUnBool
  Ty g (If e T F) | no k = no k
  Ty g [ E ] = Ty g E
  Ty g _ = no eekNotTy

  chkV : forall {n l m} -> Env n m -> (th : l <= m) -> (T : U l) -> Tm n chk -> Maybe (Va th T)
  chkV g th (Pi' S T) (la t) = yes (inr \ tr s -> chkVm g th S T t tr s)
  chkV g th Two' tt = yes (inr tt)
  chkV g th Two' ff = yes (inr ff)
  chkV g th T [ e ] with synC g e
  ... | yes (_ , ph , S , e') = subTy ph th S T e'
  ... | _ = no chkV[]
  chkV g th T _ = no chkVCatch

  chkVm : forall {n l m l'} {ph : m <= l'} {ps : l <= l'} →
        (Env n m) ->
        (th : l <= m) (S : U l)
        (T : forall {m'} (ps' : l <= m') -> Nm m' syn + Go ps' S -> Maybe (U m')) ->
        Tm (su n) chk ->
        Tr th ph ps -> (s : Nm l' syn + Go ps S) -> Vm (T ps s)
  chkVm {ps = ps} g th S T t tri s with T ps s
  chkVm {ph = ph} {ps = ps} g th S T t tri s | yes T' = chkV (snoc (thEnv g ph) (_ , ps , S , s)) oi T' t
  chkVm {ps = ps} g th S T t tri s | no _ = <>

  synC : forall {n m} -> Env n m -> Tm n syn -> Maybe (Cell m)
  synC g (e $ s) with synC g e
  synC g (e $ s) | yes (_ , th , Pi' S' T' , inl e') =
    chkV g th S' s >>= \ s' -> stop S' th s' >>= \ s0 ->
    T' th s' >>= \ Ts ->
    yes (_ , oi , Ts , inl (e' $ s0))
  synC {m = m} g (e $ s) | yes (_ , th , Pi' S' T' , inr f) =
    chkV g th S' s >>= \ s' -> help (T' th s') (f (th -oi) s')
    where
      help : (w : Maybe (U m)) -> Vm w -> Maybe (Cell m)
      help (yes T) t = t >>= \ t' -> yes (_ , oi , T , t')
      help (no e) t = no (eekCodomain e)
  synC g (e $ s) | _ = no eekAppNoFun
  synC g (if P e t f) with synC g e
  synC g (if P e t f) | yes (_ , _ , Two' , inl b) =
    Ty (snoc (thEnv g (oi o')) (_ , oi , Two' , inl (va (oe os)))) P >>= \ P' -> Stop P' >>= \ Px ->
    Ty (snoc g (_ , oi , Two' , inl b))  P >>= \ Pb  -> 
    Ty (snoc g (_ , oi , Two' , inr tt)) P >>= \ Ptt -> chkV g oi Ptt t >>= \ t' -> stop Ptt oi t' >>= \ t ->
    Ty (snoc g (_ , oi , Two' , inr ff)) P >>= \ Pff -> chkV g oi Pff f >>= \ f' -> stop Pff oi f' >>= \ f ->
    yes (_ , oi , Pb , inl (if Px b t f))
  synC g (if P e t f) | yes (_ , _ , Two' , inr tt) =
    Ty (snoc g (_ , oi , Two' , inr tt)) P >>= \ Ptt -> chkV g oi Ptt t >>= \ t' ->
    yes (_  , oi , Ptt , t')
  synC g (if P e t f) | yes (_ , _ , Two' , inr ff) =
    Ty (snoc g (_ , oi , Two' , inr ff)) P >>= \ Pff -> chkV g oi Pff f >>= \ f' ->
    yes (_  , oi , Pff , f')
  synC g (if P e t f) | _ = no eekifUnBool
  synC g (va x) = yes (g x)
  synC g (t :: T) = Ty g T >>= \ T' -> chkV g oi T' t >>= \ t' -> yes (_ , oi , T' , t')
  synC _ _ = no eeksynCCatch

myTy : forall {n} -> Tm n chk
myTy = Pi Tw [ If (va (oe os)) (Pi Tw Tw) (Pi Tw (Pi Tw Tw)) ]

tryMyTy = Ty {ze}{ze} (\ ()) myTy

myNot : forall {n} -> Tm n chk
myNot = la [ if Tw (va (oe os)) ff tt ]

myAnd : forall {n} -> Tm n chk
myAnd = la (la [ if Tw (va (oe os o')) [ va (oe os) ] ff ])

myFun : forall {n} -> Tm n syn
myFun = la [ if [ If (va (oe os)) (Pi Tw Tw) (Pi Tw (Pi Tw Tw)) ] (va (oe os)) myNot myAnd ] :: myTy

myTest0 = synC {ze}{ze} (\ ()) ((la [ va (oe os) ] :: Pi Tw Tw) $ tt)
myTest1 = synC {ze}{ze} (\ ()) ((myNot :: Pi Tw Tw) $ tt)
myTest2 = synC {ze}{ze} (\ ()) ((myAnd :: Pi Tw (Pi Tw Tw)) $ tt $ tt)
myTest3 = synC {ze}{ze} (\ ()) ((myAnd :: Pi Tw (Pi Tw Tw)) $ tt $ ff)
myTest4 = synC {ze}{ze} (\ ()) ((myAnd :: Pi Tw (Pi Tw Tw)) $ ff $ ff)
myTest5 = synC {ze}{ze} (\ ()) (myFun $ tt $ tt)
myTest6 = synC {ze}{ze} (\ ()) (myFun $ ff $ tt $ tt)



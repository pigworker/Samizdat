module WTS2 where

open import LibAgda.Zero
open import LibAgda.One
open import LibAgda.Two
open import LibAgda.Nat
open import LibAgda.Fin
open import LibAgda.Comb
open import LibAgda.Ix
open import LibAgda.Sg
open import LibAgda.Cat
open import LibAgda.Eq
open import LibAgda.Bwd

data _+top (X : Set) : Set where
  #   : X -> X +top
  top : X +top

_<U_ : Nat +top -> Nat +top -> Set
top <U _ = Zero
# _ <U top = One
# i <U # j = su i <= j

_<U=_ : Nat +top -> Nat +top -> Set
_ <U= top = One
top <U= # _ = Zero
# i <U= # j = i <= j


postulate Q : Set

data Act : Set where
  type : Act
  arg  : Q -> Act
  dom  : Q -> Act


Az : Set
Az = Bwd Act

postulate
  W : Set
  _-W>_ : W -> W -> Set
  _/_ : W -> Act -> W
  wrefl : forall {w} -> w -W> w
  wtrans : forall {u v w} -> u -W> v -> v -W> w -> u -W> w
  mono : forall u w a -> u -W> w -> (u / a) -W> (w / a)
  argDom1 : forall w q -> (w / arg q) -W> (w / type / dom q)
  argDom2 : forall w q -> (w / type / dom q / type) -W> (w / arg q / type)

infixl 8 _/_ _//_

_//_ : W -> Az -> W
w // [] = w
w // (az -, q) = w // az / q

monoz : forall u w az -> u -W> w -> (u // az) -W> (w // az)
monoz u w [] uw = uw
monoz u w (az -, a) uw = mono (u // az) (w // az) a (monoz u w az uw)

postulate
  func : forall v w bz az -> v -W> w ->
        (v // bz) -W> (v // az) -> (w // bz) -W> (w // az)


record Up-Set : Set1 where
  field
    UpPred   : W -> Set
    UpClose  : (u w : W) -> u -W> w -> UpPred u -> UpPred w
  ! : Set
  ! = Sg W UpPred
open Up-Set

data Dir : Set where chk syn : Dir

data Tm (n : Nat) : Dir -> Set where
  [_]  : Tm n syn -> Tm n chk
  U    : Nat +top -> Tm n chk
  Pi   : Q -> Tm n chk -> Tm (su n) chk -> Tm n chk
  la   : Tm (su n) chk -> Tm n chk
  _::_ : Tm n chk -> Tm n chk -> Tm n syn
  #    : Fin n -> Tm n syn
  _$_  : Tm n syn -> Tm n chk -> Tm n syn

Chk : Nat -> Set
Chk n = Tm n chk
Syn : Nat -> Set
Syn n = Tm n syn

module ACT
  (I : Nat -> Set)
  (vi : ^ Fin -:> I)
  (is : ^ I -:> Syn)
  (wk : ^ I -:> (I o su))
  where
  shf : forall {m n} -> (Env m (I n)) -> Env m (I (su n))
  shf = env wk
  wkn : forall {m n} -> (Env m (I n)) -> Env (su m) (I (su n))
  wkn g = shf g , vi ze
  ida : forall {n} -> Env n (I n)
  ida {ze}   = <>
  ida {su n} = wkn ida
  act : forall {m n d} -> (Env m (I n)) -> Tm m d -> Tm n d
  act g [ t ]      = [ act g t ]
  act g (U h)      = U h
  act g (Pi q S T) = Pi q (act g S) (act (wkn g) T)
  act g (la t)     = la (act (wkn g) t)
  act g (t :: T)   = act g t :: act g T
  act g (# i)      = is (proj i g)
  act g (f $ s)    = act g f $ act g s

module REN = ACT Fin id # su
ren : forall {m n d} -> (Env m (Fin n)) -> Tm m d -> Tm n d
ren = REN.act

wkr : forall {m n} -> m <= n -> Env m (Fin n)
wkr {ze} mn = <>
wkr {su m} {ze} ()
wkr {su m} {su n} mn = REN.shf (wkr mn) , fin m mn

open MODAL Nat<=
open Cat _ Nat<=

sucr : forall {n} -> Env n (Fin (su n))
sucr = let open REN in shf ida

module SUB = ACT Syn # id (ren sucr)
sub : forall {m n d} -> (Env m (Syn n)) -> Tm m d -> Tm n d
sub = SUB.act

Cx : Nat -> Set
Cx ze      = One
Cx (su n)  = Cx n * W * Chk n

projW : forall {n} -> Cx n -> Fin n -> W
projW (_ , (u , _)) ze = u
projW (G , _)   (su i) = projW G i

projT : forall {n} -> Cx n -> Fin n -> Chk n
projT (_ , (_ , S)) ze = ren sucr S
projT (G , _) (su i) = ren sucr (projT G i)

_%_ : forall {n d} -> Tm (su n) d -> Tm n syn -> Tm n d
t % e = sub (SUB.ida , e) t

data Reds {n} : forall {d} -> Tm n d -> Tm n d -> Set where

  beta : forall {q t t' S S' T T' s s'} ->
           Reds t t' -> Reds S S' -> Reds T T' -> Reds s s' ->
           Reds ((la t :: Pi q S T) $ s) ((t' :: T') % (s' :: S'))

  upsi : forall {t t' T} ->
           Reds t t' ->
           Reds [ t :: T ] t'

  [_] : forall {e e'} ->
          Reds e e' ->
          Reds [ e ] [ e' ]

  U : forall i -> Reds (U i) (U i)

  Pi : forall {q S S' T T'} ->
          Reds S S' -> Reds T T' ->
          Reds (Pi q S T) (Pi q S' T')

  _::_ : forall {t t' T T'} ->
          Reds t t' -> Reds T T' ->
          Reds (t :: T) (t' :: T')

  # : forall i -> Reds (# i) (# i)

  _$_ : forall {f f' s s'} ->
        Reds f f' -> Reds s s' ->
        Reds (f $ s) (f' $ s')

  

data SUBTY {n}(G : Cx n)(w : W) : Chk n -> Chk n -> Set where
  -- comparing two types which should both be valid in w [type]

  uniCum : forall {i j} -> i <U= j -> SUBTY G w (U i) (U j)

  piSub : forall {q S S' T T'} ->
    SUBTY G (w / dom q / type) S' S ->
    SUBTY (G , (w / dom q , S')) w T T' ->
  ------------------------------------------
    SUBTY G w (Pi q S T) (Pi q S' T')

  neRefl : forall {E} -> SUBTY G w [ E ] [ E ]

data CHK {n}(G : Cx n)(w : W) : Chk n -> Chk n -> Set
data SYN {n}(G : Cx n)(w : W) : Syn n -> Chk n -> Set

data CHK {n} G w where


  pre : forall {T T' t} ->

    Reds T T' -> CHK G w T' t ->
  --------------------------------
    CHK G w T t


  subty : forall {e S T} ->

    SYN G w e S -> SUBTY G (w / type) S T ->
  --------------------------------------------
    CHK G w T [ e ]


  U : forall {i j} ->

    i <U= j ->
  -----------------------
    CHK G w (U j) (U i)


  Pi : forall {i} q {S T} ->

    CHK G (w / dom q / type) (U i) S ->
    CHK (G , (w / dom q , S)) w (U i) T ->
  ------------------------------------------
    CHK G w (U i) (Pi q S T)


  la : forall {q S T t} ->

    CHK (G , (w / arg q , S)) w T t ->
  --------------------------------------
    CHK G w (Pi q S T) (la t)


data SYN {n} G w where


  post : forall {e S S'} ->

    SYN G w e S -> Reds S S' ->
  -------------------------------
    SYN G w e S'


  annot : forall {t T} ->

    CHK G (w / type) (U top) T -> CHK G w T t ->
  ------------------------------------------------
    SYN G w (t :: T) T


  var : forall i ->

    projW G i -W> w ->
  -----------------------------
    SYN G w (# i) (projT G i)


  _$_ : forall {q S T f s} ->

    SYN G w f (Pi q S T) -> CHK G (w / arg q) S s ->
  ----------------------------------------------------
    SYN G w (f $ s) (T % (s :: S))

CxAz : Nat -> Set
CxAz ze = One
CxAz (su n) = CxAz n * ((W + Az) * Chk n)

cxAz : forall n -> W -> CxAz n -> Cx n
cxAz ze w <> = <>
cxAz (su n) w (GAz , x  , S) = cxAz n w GAz , (hit x , S) where
  hit : W + Az -> W
  hit (tt , u) = u
  hit (ff , az) = w // az

wSUBTY : forall {n} (G : CxAz n) {v S T w} az -> v -W> w ->
         SUBTY (cxAz n v G) (v // az) S T -> SUBTY (cxAz n w G) (w // az) S T
wSUBTY G az vw (uniCum ij) = uniCum ij
wSUBTY G az vw (piSub S'S TT') =
  piSub (wSUBTY G ((az -, dom _) -, type) vw S'S)
        (wSUBTY (G , ((ff , (az -, dom _)) , _)) az vw TT')
wSUBTY G az vw neRefl = neRefl

wCHK : forall {n} (G : CxAz n) {v T t w} az -> v -W> w ->
         CHK (cxAz n v G) (v // az) T t -> CHK (cxAz n w G) (w // az) T t
wSYN : forall {n} (G : CxAz n) {v e S w} az -> v -W> w ->
         SYN (cxAz n v G) (v // az) e S -> SYN (cxAz n w G) (w // az) e S

wCHK G az vw (pre TT' T't) = pre TT' (wCHK G az vw T't)
wCHK G az vw (subty eS ST) =
  subty (wSYN G az vw eS) (wSUBTY G (az -, type) vw ST)
wCHK G az vw (U x) = U x
wCHK G az vw (Pi q US UT) =
  Pi q (wCHK G ((az -, dom q) -, type) vw US)
    (wCHK (G , (ff , (az -, dom q)) , _) az vw UT)
wCHK G az vw (la Tt) =
  la (wCHK (G , (ff , (az -, arg _)) , _) az vw Tt)

wVAR : forall {n} (G : CxAz n) {v w} i az -> v -W> w ->
       projW (cxAz n v G) i -W> (v // az) ->
       projW (cxAz n w G) i -W> (w // az) *
       projT (cxAz n w G) i == projT (cxAz n v G) i
wVAR (G , (tt , u) , S) ze az vw u-vaz = wtrans u-vaz (monoz _ _ az vw) , refl
wVAR (G , (ff , bz) , S) ze az vw u-vaz = func _ _ bz az vw u-vaz , refl
wVAR (G , _ ) (su i) az vw u-vaz with wVAR G i az vw u-vaz
wVAR (G , (_ , _) , _) (su i) az vw u-vaz | u-waz , pq
  rewrite pq = u-waz , refl

wSYN G az vw (post eS SS') = post (wSYN G az vw eS) SS'
wSYN G az vw (annot US Ss) =
  annot (wCHK G (az -, type) vw US) (wCHK G az vw Ss)
wSYN {n} G {v}{_}{.(projT (cxAz n v G) i)}{w} az vw (var i u-vaz)
  with wVAR G i az vw u-vaz
... | u-waz , pq = subst pq (SYN _ _ _) (var i u-waz)
wSYN G az vw (eST $ Ss) = wSYN G az vw eST $ wCHK G (az -, arg _) vw Ss

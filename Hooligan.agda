module Hooligan where

data _==_ {X : Set}(x : X) : X -> Set where
  refl : x == x

re : {X : Set}(x : X) -> x == x
re x = refl

_=$=_ : forall {X Y : Set}{f g : X -> Y}{s t : X} ->
        f == g -> s == t -> f s == g t
refl =$= refl = refl
infixl 2 _=$=_

_-=-_ : forall {X}{a b c : X} -> a == b -> b == c -> a == c
refl -=- q = q

_-=~_ : forall {X}{a b c : X} -> a == b -> c == b -> a == c
q -=~ refl = q

record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg
_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T
pattern !_ t = _ , t
infixr 4 !_ _,_ _*_

uc : forall {S T}{P : Sg S T -> Set} ->
     ((s : S)(t : T s) -> P (s , t)) ->
     (x : Sg S T) -> P x
uc k (s , t) = k s t

uc!_ : forall {S T}{P : Sg S T -> Set} ->
     ({s : S}(t : T s) -> P (s , t)) ->
     (x : Sg S T) -> P x
uc!_ k (s , t) = k {s} t
infixr 4 uc!_

data Bwd (K : Set) : Set where
  [] : Bwd K
  _-,_ : Bwd K -> K -> Bwd K

_++_ : forall {K} -> Bwd K -> Bwd K -> Bwd K
xz ++ [] = xz
xz ++ (yz -, y) = (xz ++ yz) -, y

infixl 6 _++_ _-,_

data _<=_ {K} : Bwd K -> Bwd K -> Set where
  _o' : forall {iz jz k} -> iz <= jz ->  iz       <= (jz -, k)
  _os : forall {iz jz k} -> iz <= jz -> (iz -, k) <= (jz -, k)
  oz : [] <= []
infixl 5 _o' _os

`o : forall {K}{iz jz : Bwd K}{i} -> (iz -, i) <= jz -> iz <= jz
`o (th o') = `o th o'
`o (th os) = th o'

_<-_ : forall {K} -> K -> Bwd K -> Set
k <- kz = ([] -, k) <= kz

oi : forall {K}{kz : Bwd K} -> kz <= kz
oi {_} {[]} = oz
oi {_} {_ -, _} = oi os

oe : forall {K}{kz : Bwd K} -> [] <= kz
oe {_} {[]} = oz
oe {_} {_ -, _} = oe o'

_-_ : forall {K}{iz jz kz : Bwd K} -> iz <= jz -> jz <= kz -> iz <= kz
th - (ph o') = (th - ph) o'
(th o') - (ph os) = (th - ph) o'
(th os) - (ph os) = (th - ph) os
oz - oz = oz

infixr 4 _-_

oe1 : forall {K}{kz : Bwd K}{th ph : [] <= kz} -> th == ph
oe1 {th = th o'} {ph = ph o'} = re _o' =$= oe1
oe1 {th = oz} {ph = oz} = refl

`oq : forall {K}{iz jz kz : Bwd K}{j}
      (th : iz <= jz)(ph : (jz -, j) <= kz) -> (th - `o ph) == (th o' - ph)
`oq th (ph o') = re _o' =$= `oq th ph
`oq th (ph os) = refl

asso : forall {K}{hz iz jz kz : Bwd K}(th : hz <= iz)(ph : iz <= jz)(ps : jz <= kz) ->
  ((th - ph) - ps) == (th - (ph - ps))
asso th ph (ps o') = re _o' =$= asso th ph ps
asso th (ph o') (ps os) = re _o' =$= asso th ph ps
asso (th o') (ph os) (ps os) = re _o' =$= asso th ph ps
asso (th os) (ph os) (ps os) = re _os =$= asso th ph ps
asso oz oz oz = refl

record Kind (I : Set) : Set where
  inductive
  constructor _=>_
  field
    scope : Bwd (Kind I)
    sort  : I
open Kind

data Tm {I}(C M : Kind I -> Set)(i : I)(G : Bwd (Kind I)) : Set
data Sp {I}(C M : Kind I -> Set)(G : Bwd (Kind I)) : Bwd (Kind I) -> Set where
  [] : Sp C M G []
  _-,_ : forall {kz jz i} -> Sp C M G kz -> Tm C M i (G ++ jz) -> Sp C M G (kz -, (jz => i))

data Tm {I} C M i G where
  _`_ : forall {jz} -> C (jz => i) -> Sp C M G jz -> Tm C M i G
  _$_ : forall {jz} -> (jz => i) <- G -> Sp C M G jz -> Tm C M i G
  _/_ : forall {jz} -> M (jz => i) -> jz <= G -> Tm C M i G

_oss_ : forall {K}{iz jz : Bwd K} -> iz <= jz -> (kz : Bwd K) -> (iz ++ kz) <= (jz ++ kz)
th oss []        = th
th oss (kz -, k) = th oss kz os

_o''_ : forall {K}{iz jz : Bwd K} -> iz <= jz -> (kz : Bwd K) -> iz <= (jz ++ kz)
th o'' []      = th
th o'' kz -, k = th o'' kz o'

infixl 5 _oss_ _o''_

thin : forall {I}{C M}{i : I}{G D} -> Tm C M i G -> G <= D -> Tm C M i D
thins : forall {I}{C M G D}{jz : Bwd (Kind I)} -> Sp C M G jz -> G <= D -> Sp C M D jz
thin (c ` ts) th = c ` thins ts th
thin (i $ ts) th = (i - th) $ thins ts th
thin (x / ph) th = x / (ph - th)
thins [] th = []
thins (_-,_ {jz = jz} ts t) th = thins ts th -, thin t (th oss jz)

stan : forall {I}{C M N}{i : I}{G} -> Tm C M i G ->
       (forall {jz i} -> M (jz => i) -> Tm C N i jz)
       -> Tm C N i G
stans : forall {I}{C M N G}{kz : Bwd (Kind I)} -> Sp C M G kz ->
        (forall {jz i} -> M (jz => i) -> Tm C N i jz)
        -> Sp C N G kz
stan (c ` ts) sg = c ` stans ts sg
stan (i $ ts) sg = i $ stans ts sg
stan (x / th) sg = thin (sg x) th
stans [] sg = []
stans (_-,_ {jz = jz} ts t) sg = stans ts sg -, stan t sg

data Tri {K} : forall {iz jz kz : Bwd K} ->
               iz <= jz -> jz <= kz -> iz <= kz -> Set where
  _t-'' : forall {k iz jz kz}{th : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
          Tri th ph ps -> Tri {kz = kz -, k} th (ph o') (ps o')
  _t's' : forall {k iz jz kz}{th : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
          Tri th ph ps -> Tri {kz = kz -, k} (th o') (ph os) (ps o')
  _tsss : forall {k iz jz kz}{th : iz <= jz}{ph : jz <= kz}{ps : iz <= kz} ->
          Tri th ph ps -> Tri {kz = kz -, k} (th os) (ph os) (ps os)
  tzzz  : Tri oz oz oz
infixl 5 _t-'' _t's' _tsss

mkTri : forall {K}{iz jz kz : Bwd K}(th : iz <= jz)(ph : jz <= kz) ->
        Tri th ph (th - ph)
mkTri th (ph o') = mkTri th ph t-''
mkTri (th o') (ph os) = mkTri th ph t's'
mkTri (th os) (ph os) = mkTri th ph tsss
mkTri oz oz = tzzz

triDet : forall {K}{iz jz kz : Bwd K}
         {th : iz <= jz}{ph : jz <= kz}{ps ps' : iz <= kz} ->
         Tri th ph ps -> Tri th ph ps' -> ps == ps'
triDet (t t-'') (t' t-'') with triDet t t'
triDet (t t-'') (t' t-'') | refl = refl
triDet (t t's') (t' t's') with triDet t t'
triDet (t t's') (t' t's') | refl = refl
triDet (t tsss) (t' tsss) with triDet t t'
triDet (t tsss) (t' tsss) | refl = refl
triDet tzzz tzzz = refl

_-oi : forall {K}{iz jz : Bwd K}(th : iz <= jz) -> Tri th oi th
(th o') -oi = (th -oi) t's'
(th os) -oi = (th -oi) tsss
oz -oi = tzzz

data Maybe (X : Set) : Set where
  yes : X -> Maybe X
  no  : Maybe X

_>>=_ : forall {X Y} -> Maybe X -> (X -> Maybe Y) -> Maybe Y
yes x >>= k = k x
no    >>= _ = no
infixr 4 _>>=_

subset : forall {K}{iz jz kz : Bwd K}(ps : iz <= kz)(ph : jz <= kz) ->
         Maybe (Sg (iz <= jz) \ th -> Tri th ph ps)
subset (ps o') (ph o') = subset ps ph >>= uc! \ t -> yes (! t t-'')
subset (ps o') (ph os) = subset ps ph >>= uc! \ t -> yes (! t t's')
subset (ps os) (ph o') = no
subset (ps os) (ph os) = subset ps ph >>= uc! \ t -> yes (! t tsss)
subset oz oz = yes (! tzzz)

data Pruning {I} : Bwd (Kind I) -> Bwd (Kind I) -> Set where
  _-,_ : forall {kz kz' jz jz' i} ->
         Pruning kz kz' -> jz <= jz' ->
         Pruning (kz -, (jz => i)) (kz' -, (jz' => i))
  [] : Pruning [] []

prunei : forall {I}{kz : Bwd (Kind I)} -> Pruning kz kz
prunei {kz = []} = []
prunei {kz = kz -, (jz => i)} = prunei -, oi

pruneProj : forall {I}{kz kz' : Bwd (Kind I)} ->
            Pruning kz kz' -> forall {jz' i} -> (jz' => i) <- kz' ->
            Sg _ \ jz -> (jz <= jz') * ((jz => i) <- kz)
pruneProj (p -, _) (x' o') with pruneProj p x'
... | ! th , x = ! th , x o'
pruneProj (p -, th) (x' os) = ! th , oe os


pruneStan : forall {I C}{kz kz' : Bwd (Kind I)} -> Pruning kz kz' ->
            forall {jz i} -> (jz => i) <- kz' ->
              Tm C (_<- kz) i jz
pruneStan p x' = let ! th , x = pruneProj p x' in x / th

pullback : forall {K}{iz jz kz : Bwd K}(th' : iz <= kz)(ph' : jz <= kz) ->
           Sg _ \ hz ->
           Sg (hz <= iz) \ th -> Sg (hz <= kz) \ ps -> Sg (hz <= jz) \ ph ->
           Tri th th' ps * Tri ph ph' ps
pullback (th' o') (ph' o') with pullback th' ph'
... | ! ! ! ! s , t = ! ! ! ! s t-'' , t t-''
pullback (th' o') (ph' os) with pullback th' ph'
... | ! ! ! ! s , t = ! ! ! ! s t-'' , t t's'
pullback (th' os) (ph' o') with pullback th' ph'
... | ! ! ! ! s , t = ! ! ! ! s t's' , t t-''
pullback (th' os) (ph' os) with pullback th' ph'
... | ! ! ! ! s , t = ! ! ! ! s tsss , t tsss
pullback oz oz = _ , oz , oz , oz , tzzz , tzzz

data PTri {I} : {iz jz kz : Bwd (Kind I)}
                (a : Pruning iz jz)(b : Pruning jz kz)(c : Pruning iz kz) -> Set where
  _-,_ : forall {iz jz kz iz' jz' kz' : Bwd (Kind I)}{i}
         {a : Pruning iz jz}{b : Pruning jz kz}{c : Pruning iz kz} ->
         {th : iz' <= jz'}{ph : jz' <= kz'}{ps : iz' <= kz'} ->
         PTri a b c -> Tri th ph ps ->
         PTri {kz = _ -, (_ => i)} (a -, th) (b -, ph) (c -, ps)
  [] : PTri [] [] []

ppullback : forall {I}{iz jz kz : Bwd (Kind I)} ->
            (p' : Pruning iz kz)(q' : Pruning jz kz) ->
            Sg _ \ hz ->
            Sg (Pruning hz iz) \ p ->
            Sg (Pruning hz kz) \ m ->
            Sg (Pruning hz jz) \ q ->
            PTri p p' m * PTri q q' m
ppullback (p' -, th') (q' -, ph') with ppullback p' q' | pullback th' ph'
... | ! ! ! ! az , bz | ! ! ! ! a , b = ! ! ! ! (az -, a) , (bz -, b)
ppullback [] [] = ! ! ! ! [] , []


prune1 : forall {I}{i : I}{kz' jz jz'} ->
        (ph : jz <= jz')(x' : (jz' => i) <- kz') ->
        Sg _ \ kz -> Sg ((jz => i) <- kz) \ x -> Sg (Pruning kz kz') \ p ->
        pruneProj p x' == (! ph , x)
prune1 ph (x' o') with prune1 ph x'
... | ! x , p , q =
  ! (x o')
  , (p -, oi)
  , (re _ =$= q)
prune1 ph (x' os) = ! (oe os) , (prunei -, ph) , refl

pTriProj : forall {I}{jz kz hz'}{i : I}(q : Pruning jz kz)(x' : (hz' => i) <- kz) ->
           forall {hz1 th1 x1} -> pruneProj q x' == (hz1 , th1 , x1) ->
           forall {iz hz}
           (p : Pruning iz jz)(r : Pruning iz kz) -> PTri p q r ->
           (x : (hz => i) <- jz) ->
           forall {hz0 hz2 th0 th2 x0 x2} ->
           (hz0 , th0 , x0) == pruneProj p x -> 
           (hz2 , th2 , x2) == pruneProj r x' ->
           forall {G} -> (ph : hz <= G)(ph' : hz' <= G) ->
           forall {C} ->
           (_/_ {C = C}{M = (_<- jz)} x ph) == (x1 / (th1 - ph')) -> 
           Sg (hz0 == hz2) \ { refl ->
             Sg (hz1 == hz) \ { refl ->
               x0 == x2 * Tri th0 th1 th2 } }
pTriProj (q -, _) (x' o') a (p -, _) (r -, _) (pqr -, _) x b c ph ph' d
  with pruneProj q x' | pTriProj q x' refl
pTriProj (q -, _) (x' o') refl (p -, _) (r -, _) (pqr -, _) .(x o') b c .(d1 - ph') ph' {C = C} refl | d0 , d1 , x | l
  with pruneProj p x | pruneProj r x' | l p r pqr x refl refl _ ph' {C = C} refl
pTriProj (q -, _) (x' o') refl (p -, _) (r -, _) (pqr -, _) .(x o') refl refl .(d1 - ph') ph' {C} refl | d0 , d1 , x | l | e0 , e1 , e2 | .e0 , f1 , .e2 | refl , refl , refl , g = refl , refl , refl , g
pTriProj ._ (x' os) refl ._ ._ (pqr -, t) .(oe os) refl refl ._ ph' refl
  = refl , refl , refl , t

pTriLemma : forall {I C}{iz jz kz G D : Bwd (Kind I)}{i}
            {p : Pruning iz jz}{q : Pruning jz kz}{r : Pruning iz kz} ->
            PTri p q r -> (th : G <= D)
            (t : Tm C (_<- jz) i G)(t' : Tm C (_<- kz) i D) ->
            thin t th == stan t' (pruneStan q) ->
            thin (stan t (pruneStan p)) th == stan t' (pruneStan r)
pTriLemmas : forall {I C}{iz jz kz G D : Bwd (Kind I)}{hz}
             {p : Pruning iz jz}{q : Pruning jz kz}{r : Pruning iz kz} ->
             PTri p q r -> (th : G <= D)
             (ts : Sp C (_<- jz) G hz)(ts' : Sp C (_<- kz) D hz) ->
             thins ts th == stans ts' (pruneStan q) ->
             thins (stans ts (pruneStan p)) th == stans ts' (pruneStan r)
pTriLemma pqr th (c ` ts) (c' ` ts') q with thins ts th | pTriLemmas pqr th ts
pTriLemma pqr th (c ` ts) (c' ` ts') refl | ._ | b = re (c `_) =$= b ts' refl
pTriLemma pqr th (c ` ts) (_ $ _) ()
pTriLemma pqr th (c ` ts) (_ / _) ()
pTriLemma pqr th (i $ ts) (_ ` _) ()
pTriLemma pqr th (i $ ts) (i' $ ts') q with thins ts th | pTriLemmas pqr th ts
pTriLemma pqr th (i $ ts) (.(i - th) $ ts') refl | ._ | b
  = re ((i - th) $_) =$= b ts' refl
pTriLemma pqr th (i $ ts) (_ / _) ()
pTriLemma pqr th (x / ph) (_ ` _) ()
pTriLemma pqr th (x / ph) (_ $ _) ()
pTriLemma {C = C} {p = p}{q}{r} pqr th (x / ph) (x' / ph') eq
  with ph - th | mkTri ph th | pruneProj q x' | pTriProj q x' refl
pTriLemma {C = C} {p = p} {q} {r} pqr th (.x / ph) (x' / ph') refl
  | .(d1 - ph') | t | d0 , d1 , x | l with pruneProj p x | pruneProj r x' | l p r pqr x refl refl (d1 - ph') ph' {C = C} refl
pTriLemma {C = C} {p = p} {q} {r} pqr th (.x / ph) (x' / ph') refl | .(d1 - ph') | t | d0 , d1 , x | l | e0 , e1 , e2 | .e0 , f1 , .e2 | refl , refl , refl , t' =
  re (e2 /_) =$= ((asso e1 ph th -=- ((re (e1 -_) =$= triDet (mkTri ph th) t) -=~ asso e1 d1 ph')) -=- (re (_- ph') =$= triDet (mkTri e1 d1) t'))

pTriLemmas pqr th [] [] q = refl
pTriLemmas pqr th (_-,_ {jz = jz} ts t) (ts' -, t') q
  with thins ts th | pTriLemmas pqr th ts ts'
     | thin t (th oss jz) | pTriLemma pqr (th oss jz) t t'
pTriLemmas pqr th (_-,_ {jz = jz} ts t) (ts' -, t') refl | ._ | b | ._ | d
  = re _-,_ =$= b refl =$= d refl
            
strengthen : forall {I C}{i : I}{kz' G D}
             (th' : G <= D)(t' : Tm C (_<- kz') i D) ->
  Maybe (Sg _ \ kz -> Sg (Tm C (_<- kz) i G) \ t -> Sg (Pruning kz kz') \ p ->
         thin t th' == stan t' (pruneStan p))
strengthens : forall {I C}{jz : Bwd (Kind I)}{kz' G D}
              (th' : G <= D)(ts' : Sp C (_<- kz') D jz) ->
  Maybe (Sg _ \ kz -> Sg (Sp C (_<- kz) G jz) \ ts -> Sg (Pruning kz kz') \ p ->
         thins ts th' == stans ts' (pruneStan p))
strengthen th' (c ` ts') = strengthens th' ts' >>= uc! uc \ ts -> uc \ p q' ->
  yes (! (c ` ts) , p , (re (c `_) =$= q'))
strengthen th' (i' $ ts') =
  subset i' th' >>= uc \ i q -> strengthens th' ts' >>= uc! uc \ ts -> uc \ p q' ->
  yes (! (i $ ts) , p , (re _$_ =$= triDet (mkTri i th') q =$= q'))
strengthen th' (x' / ph') with pullback th' ph'
... | ! th , ps , ph , q , q' with prune1 ph x'
... | ! x , p , q'' = yes (! (x / th) , p , help (pruneProj p x') q'') where
  help : (w : Sg _ \ hz -> (hz <= _) * ((hz => _) <- _)) ->
         w == (_ , ph , x) ->
         (x / (th - th')) == (snd (snd w) / (fst (snd w) - ph'))
  help (_ , _ , _) refl = re (x /_) =$=
    (triDet (mkTri th th') q -=- triDet q' (mkTri ph ph'))

strengthens th [] = yes (! [] , prunei , refl)
strengthens th (_-,_ {jz = jz} ts' t') =
  strengthens th ts' >>= uc! uc \ ts -> uc \ p q ->
  strengthen (th oss jz) t' >>= uc! uc \ t -> uc \ p' q' ->
  let ! u , v , u' , w , w' = ppullback p p' in
  yes (! (stans ts (pruneStan u) -, stan t (pruneStan u')) , v ,
         (re _-,_
          =$= pTriLemmas w th ts ts' q
          =$= pTriLemma w' (th oss jz) t t' q'))

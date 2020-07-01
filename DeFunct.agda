module DeFunct where

module _ {l}{X : Set l} where

 data _~_ (x : X) : X -> Set where
   r~ : x ~ x

 infix 40 _-~-_
 infix 41 _~o

 _~o : forall {x y} -> x ~ y -> y ~ x                 -- symmetry
 r~ ~o = r~

 _-~-_ : forall {x y z} -> x ~ y -> y ~ z -> x ~ z    -- transitivity
 r~ -~- q = q

 infixr 30 _~[_>_ _<_]~_
 infixr 31 _[QED]

 _~[_>_ : forall x {y z} -> x ~ y -> y ~ z -> x ~ z
 x ~[ q0 > q1 = q0 -~- q1

 _<_]~_ : forall x {y z} -> y ~ x -> y ~ z -> x ~ z
 x < q0 ]~ q1 = q0 ~o -~- q1

 _[QED] : forall x -> x ~ x
 x [QED] = r~

{-# BUILTIN EQUALITY _~_ #-}

rf : forall {k}{X : Set k} (x : X) -> x ~ x
rf x = r~

module _ {k l}{X : Set k}{Y : Set l} where
 
 infixl 2 _~$~_ _$~_ _~$   -- "associating to the left, rather as we all did
                           -- in the sixties" (Roger Hindley)
  
 _~$~_ : {f g : X -> Y}{a b : X} -> f ~ g -> a ~ b -> f a ~ g b
 r~ ~$~ r~ = r~
  
 _$~_ : {a b : X}            (f : X -> Y) -> a ~ b -> f a ~ f b
 f $~ q = rf f ~$~ q

 _~$ : {f g : X -> Y}{a : X} ->     f ~ g          -> f a ~ g a
 f ~$ = f ~$~ r~

record One : Set where constructor <>

record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_ public

_*_ : Set -> Set -> Set
S * T = S >< \ _ -> T

sym : forall {l}{X : Set l}{x y : X} ->
  x ~ y -> y ~ x
sym r~ = r~

trans : forall {l}{X : Set l}{x y z : X} ->
  x ~ y -> y ~ z -> x ~ z
trans r~ q = q

resp : forall {k l}{X : Set k}{Y : Set l} ->
  (f : X -> Y) -> forall {x0 x1 : X} -> x0 ~ x1 ->
  f x0 ~ f x1
resp f r~ = r~

subst : forall {S : Set}(T : S -> Set)
  {s0 s1 : S} -> s0 ~ s1 -> T s0 -> T s1
subst T r~ t = t

Pi : (S : Set)(T : S -> Set) -> Set
Pi S T = (s : S) -> T s

qpair : forall {S : Set}{T : S -> Set}
  {s0 s1 : S}{t0 : T s0}{t1 : T s1} ->
  (q0 : s0 ~ s1) ->
  (q1 : subst T q0 t0 ~ t1) ->
  _~_ {_}{S >< T} (s0 , t0) (s1 , t1)
qpair r~ q1 rewrite q1 = r~

uip : forall {l}{X : Set l}{x0 x1 : X}{q0 q1 : x0 ~ x1} ->
  q0 ~ q1
uip {q0 = r~}{q1 = r~} = r~

record SmolCat : Set1
  where
  field
    Obj  : Set
    Arr  : Obj -> Obj -> Set
    iden : forall {X} -> Arr X X
    comp : forall {R S T} -> Arr R S -> Arr S T -> Arr R T
    absl : forall {S T}(f : Arr S T) -> comp iden f ~ f
    absr : forall {S T}(f : Arr S T) -> comp f iden ~ f
    asso : forall {R S T U}
           (f : Arr R S)(g : Arr S T)(h : Arr T U) ->
           comp (comp f g) h ~ comp f (comp g h)

record SmolFun (A B : SmolCat) : Set
  where
  open SmolCat
  field
    Map : Obj A -> Obj B
    map : forall {S T : Obj A} ->
          Arr A S T -> Arr B (Map S) (Map T)
    mapIden : forall {X} ->
      map (iden A {X}) ~ iden B {Map X}
    mapComp : forall {R S T}(f : Arr A R S)(g : Arr A S T) ->
      map (comp A f g) ~ comp B (map f) (map g)

record Interp (C : SmolCat) : Set1 where
  open SmolCat C
  field
    ObjI : Obj -> Set
    ArrI : forall {S T} -> Arr S T -> ObjI S -> ObjI T
    idenI : forall {X}(x : ObjI X) ->
      ArrI (iden {X}) x ~ x
    compI : forall {R S T}(f : Arr R S)(g : Arr S T)
      (r : ObjI R) ->
      ArrI (comp f g) r ~ ArrI g (ArrI f r)

module _ where
  open SmolCat
  
  Discrete : Set -> SmolCat
  Obj (Discrete X) = X
  Arr (Discrete X) s t = s ~ t
  iden (Discrete X) = r~
  comp (Discrete X) r~ q = q
  absl (Discrete X) q = r~
  absr (Discrete X) r~ = r~
  asso (Discrete X) r~ q q' = r~

module _ (C : SmolCat)(F : Interp C)
  where
  open SmolCat C
  open Interp F
  Sigma : SmolCat
  SmolCat.Obj Sigma = Obj >< ObjI
  SmolCat.Arr Sigma (S , s) (T , t) = 
    Arr S T >< \ f -> ArrI f s ~ t
  SmolCat.iden Sigma {X , x} = iden , idenI x
  fst (SmolCat.comp Sigma {R , r} {S , s} {T , t} (f , q) (g , q')) = comp f g
  snd (SmolCat.comp Sigma {R , r} {S , ._} {T , ._} (f , r~) (g , r~)) = compI f g r
  SmolCat.absl Sigma (f , r~) =
    qpair (absl f) uip
  SmolCat.absr Sigma (f , r~) =
    qpair (absr f) uip
  SmolCat.asso Sigma (f , r~) (g , r~) (h , r~) =
    qpair (asso f g h) uip

{-
module _ where
  open SmolCat
  open SmolFun
  open Interp
  
  data _->Set (C : SmolCat) : Set1
  [_]I : forall {C} -> C ->Set -> Interp C

  data _->Set C where
    fae : Obj C -> C ->Set
    kon : Set -> C ->Set
    sgm : (A : C ->Set) ->
          (B : Sigma C ([ A ]I) ->Set) ->
          C ->Set
    com : {D : SmolCat}(F : SmolFun C D) ->
          D ->Set -> C ->Set

  ObjI ([_]I {C} (fae S)) T = Arr C S T
  ObjI [ kon X ]I _ = X
  ObjI [ sgm A B ]I X =
    ObjI [ A ]I X >< \ a -> ObjI [ B ]I (X , a)
  ObjI [ com F G ]I X = ObjI [ G ]I (Map F X)
  ArrI ([_]I {C} (fae S)) g f = comp C f g
  ArrI [ kon X ]I g x = x
  ArrI [ sgm A B ]I g (a , b)
    = ArrI [ A ]I g a
    , ArrI [ B ]I (g , r~) b
  ArrI [ com F G ]I g x
    = ArrI [ G ]I (map F g) x
  idenI ([_]I {C} (fae S)) f = absr C f
  idenI [ kon X ]I x = r~
  idenI ([_]I {C} (sgm A B)) {X} (a , b)
    with idenI [ A ]I a | idenI [ B ]I b
  ... | ah | bh 
     = qpair ah (trans (help _ ah r~) bh)
     where
     help : (w : ObjI [ A ]I X) (ak : w ~ a) ->
       (q : ArrI [ A ]I (iden C) a ~ w) ->
       subst (\ a -> ObjI [ B ]I (X , a)) ak
       (ArrI [ B ]I (iden C , q) b)
       ~ ArrI [ B ]I (iden C , ah) b
     help w r~ q =
       resp (\ q -> ArrI [ B ]I (iden C , q) b) uip

  idenI [ com F G ]I {X} x
    rewrite mapIden F {X} = idenI [ G ]I x
  compI ([_]I {C} (fae S)) f g e = sym (asso C e f g)
  compI [ kon X ]I f g r = r~
  compI ([_]I {C} (sgm A B)) {T = T} f g (a , b)
    with compI [ A ]I f g a
       | compI [ B ]I (f , r~) (g , r~) b
  ... | ah | bh = 
    qpair ah (trans (help _ ah r~) bh) where
      help : (w : ObjI [ A ]I T)
        (ak : ArrI [ A ]I (comp C f g) a ~ w)
        (q : ArrI [ A ]I g (ArrI [ A ]I f a) ~ w) ->
        subst (\ a -> ObjI [ B ]I (T , a)) ak
        (ArrI [ B ]I (comp C f g , r~) b)
        ~ ArrI [ B ]I
            (comp (Sigma C [ A ]I) (f , r~) (g , q)) b
      help w r~ q = 
        resp (\ q -> ArrI [ B ]I (comp C f g , q) b) uip
  compI [ com F G ]I f g r
    rewrite mapComp F f g
          = compI [ G ]I (map F f) (map F g) r
-}

{-
module _ where
  open SmolCat
  open SmolFun
  open Interp
  
  data [_->Set]->[_->Set] (C D : SmolCat) : Set1
  [_]O : forall {C D} -> [ C ->Set]->[ D ->Set]
                      -> (Obj C -> Set)
                      -> (Obj D -> Set)
  [_]I : forall {C D} -> [ C ->Set]->[ D ->Set]
                      -> Interp C
                      -> Interp D
  data Mu {C}(F : [ C ->Set]->[ C ->Set])(X : Obj C) : Set
  MuI : forall {C}(F : [ C ->Set]->[ C ->Set]) -> Interp C

  {- This ain't right! Need to have the notion of
     "decoder" to interpret the recursive positions
     in the sigma construct. -}

  data [_->Set]->[_->Set] C D where
    rec : C ~ D -> [ C ->Set]->[ D ->Set]
    hom : Obj D -> [ C ->Set]->[ D ->Set]
    kon : Set   -> [ C ->Set]->[ D ->Set]
    sgm : (A : [ C ->Set]->[ D ->Set])
          (B : [ C ->Set]->[ Sigma D ([ A ]I {!ow?!}) ->Set])
       -> [ C ->Set]->[ D ->Set]
    com : forall {E} -> SmolFun D E ->
          [ C ->Set]->[ E ->Set] ->
          [ C ->Set]->[ D ->Set]

  [ rec r~ ]O R X = R X
  [_]O {D = D} (hom S) R X = Arr D S X
  [ kon K ]O _ _  = K
  [ sgm A B ]O R X =
    [ A ]O R X >< \ a -> [ B ]O R (X , {!decode a?!})
  [ com F G ]O R X = [ G ]O R (Map F X)

  ObjI ([ F ]I R) = [ F ]O (ObjI R) 
  ArrI ([ F ]I R) = {!!}
  idenI ([ F ]I R) = {!!}
  compI ([ F ]I R) = {!!}

  data Mu {C} F X where
    [_] : [ F ]O (Mu F) X -> Mu F X
 
  MuI F = {!!}
-}

-- Chicken out. Do an inductive version...

module _ where
  open SmolCat
  open SmolFun
  open Interp
  
  data [_->Set]->[_->Set] (C D : SmolCat) : Set1 where
    rec : C ~ D -> [ C ->Set]->[ D ->Set]
    hom : Obj D -> [ C ->Set]->[ D ->Set]
    com : forall {E} -> SmolFun D E ->
          [ C ->Set]->[ E ->Set] ->
          [ C ->Set]->[ D ->Set]
    sgm : (A : Set)
          (B : A -> [ C ->Set]->[ D ->Set])
       -> [ C ->Set]->[ D ->Set]
    one : [ C ->Set]->[ D ->Set]
    prd : (S T : [ C ->Set]->[ D ->Set])
       -> [ C ->Set]->[ D ->Set]

  [_]O : forall {C D} -> [ C ->Set]->[ D ->Set]
                      -> (Obj C -> Set)
                      -> (Obj D -> Set)
  [ rec r~ ]O R X = R X
  [_]O {D = D} (hom S) _ X = Arr D S X
  [ com F G ]O R X = [ G ]O R (Map F X)
  [ sgm A B ]O R X = A >< \ a -> [ B a ]O R X
  [ one ]O R X = One
  [ prd F G ]O R X = [ F ]O R X * [ G ]O R X
                      
  [_]I : forall {C D} -> [ C ->Set]->[ D ->Set]
                      -> Interp C
                      -> Interp D
  ObjI ([ F ]I R) = [ F ]O (ObjI R)
  
  ArrI ([ rec r~ ]I R) = ArrI R
  idenI ([ rec r~ ]I R) x = idenI R x
  compI ([ rec r~ ]I R) f g x = compI R f g x
  
  ArrI ([_]I {D = D} (hom S) R) g f = comp D f g
  idenI ([_]I {D = D} (hom S) R) f = absr D f
  compI ([_]I {D = D} (hom S) R) f g e = sym (asso D e f g)
  
  ArrI ([ com F G ]I R) f = ArrI ([ G ]I R) (map F f)
  idenI ([_]I {D = D} (com {E} F G) R) x =
       ArrI G' (map F (iden D)) x
         ~[ ArrI G' $~ mapIden F ~$~ rf x >
       ArrI G' (iden E) x
         ~[ idenI G' x >
       x
         [QED]
    where G' = [ G ]I R
  compI ([_]I {D = D} (com {E} F G) R) f g e =
       ArrI G' (map F (comp D f g)) e
         ~[ ArrI G' $~ mapComp F _ _ ~$~ rf e >
       ArrI G' (comp E (map F f) (map F g)) e
         ~[ compI G'  _ _ _ >
       ArrI G' (map F g) (ArrI G' (map F f) e)
         [QED]
    where G' = [ G ]I R
    
  ArrI ([ sgm A B ]I R) f (a , s) = a , ArrI ([ B a ]I R) f s
  idenI ([ sgm A B ]I R) (a , x) = (a ,_) $~ idenI ([ B a ]I R) x
  compI ([ sgm A B ]I R) f g (a , r) =
    (a ,_) $~ compI ([ B a ]I R) f g r
    
  ArrI ([ one ]I R) = _
  idenI ([ one ]I R) x = r~
  compI ([ one ]I R) f g x = r~
  
  ArrI ([ prd F G ]I R) f (sF , sG) =
    ArrI ([ F ]I R) f sF , ArrI ([ G ]I R) f sG
  idenI ([ prd F G ]I R) (xF , xG) = 
    _,_ $~ idenI ([ F ]I R) xF ~$~ idenI ([ G ]I R) xG
  compI ([ prd F G ]I R) f g (xF , xG) =
    _,_ $~ compI ([ F ]I R) f g xF ~$~ compI ([ G ]I R) f g xG

{- inevitable, termination checker complains
  module _ {C}(F : [ C ->Set]->[ C ->Set]) where
    data Mu (X : Obj C) : Set where
      [_] : [ F ]O Mu X -> Mu X

    MuI : Interp C
    ObjI MuI = Mu
    ArrI MuI f [ rF ] = [ ArrI ([ F ]I MuI) f rF ]
    idenI MuI = {!!}
    compI MuI = {!!}
-}

-- the inevitable inlining of map, etc
  module _ {C} where
    data Mu (F : [ C ->Set]->[ C ->Set])(X : Obj C) : Set where
      [_] : [ F ]O (Mu F) X -> Mu F X

    mapMu : forall {F}{S T} -> Arr C S T -> Mu F S -> Mu F T
    mapMuGo : forall {F D}(G : [ C ->Set]->[ D ->Set]) ->
               forall {S T} -> Arr D S T ->
               [ G ]O (Mu F) S -> [ G ]O (Mu F) T
    mapMu {F} f [ sF ] = [ mapMuGo F f sF ]
    mapMuGo (rec r~) f x = mapMu f x
    mapMuGo {_}{D} (hom S) g f = comp D f g
    mapMuGo (com G H) f x = mapMuGo H (map G f) x
    mapMuGo (sgm A B) f (a , sB) = a , mapMuGo (B a) f sB
    mapMuGo one f x = <>
    mapMuGo (prd G H) f (sG , sH) = mapMuGo G f sG , mapMuGo H f sH

    mapIMu : forall {F}{X}(x : Mu F X) -> mapMu (iden C) x ~ x
    mapIMuGo : forall {D F}(G : [ C ->Set]->[ D ->Set]) ->
               forall {X} ->
               (x : [ G ]O (Mu F) X) ->
               mapMuGo G (iden D) x ~ x
    mapIMu {F} [ xF ] = [_] $~ mapIMuGo F xF
    mapIMuGo (rec r~) x = mapIMu x
    mapIMuGo {D} (hom S) f = absr D f
    mapIMuGo {D} (com {E} G H) x =
      mapMuGo H (map G (iden D)) x
         ~[ mapMuGo H $~ mapIden G ~$~ rf x >
      mapMuGo H (iden E) x
         ~[ mapIMuGo H x >
      x
         [QED]
    mapIMuGo (sgm A B) (a , xB) = (a ,_) $~ mapIMuGo (B a) xB
    mapIMuGo one x = r~
    mapIMuGo (prd G H) (xG , xH) = 
      _,_ $~ mapIMuGo G xG ~$~ mapIMuGo H xH

    mapCMu : forall {F R S T}
      (f : Arr C R S) (g : Arr C S T) (r : Mu F R) ->
      mapMu (comp C f g) r ~ mapMu g (mapMu f r)
    mapCMuGo : forall {D F R S T}(G : [ C ->Set]->[ D ->Set])
      (f : Arr D R S) (g : Arr D S T) (r : [ G ]O (Mu F) R) ->
      mapMuGo G (comp D f g) r ~ mapMuGo G g (mapMuGo G f r)
    mapCMu {F} f g [ rF ] = [_] $~ mapCMuGo F f g rF
    mapCMuGo (rec r~) f g rG = mapCMu f g rG
    mapCMuGo {D} (hom S) f g e = sym (asso D e f g)
    mapCMuGo {D} (com {E} G H) f g rH =
       mapMuGo H (map G (comp D f g)) rH
         ~[ mapMuGo H $~ mapComp G _ _ ~$~ rf rH >
       mapMuGo H (comp E (map G f) (map G g)) rH
         ~[ mapCMuGo H  _ _ _ >
       mapMuGo H (map G g) (mapMuGo H (map G f) rH)
         [QED]
    mapCMuGo (sgm A B) f g (a , rB) =
      (a ,_) $~ mapCMuGo (B a) f g rB
    mapCMuGo one f g _ = r~
    mapCMuGo (prd G H) f g (rG , rH) =
      _,_ $~ mapCMuGo G f g rG ~$~ mapCMuGo H f g rH

    MuI : [ C ->Set]->[ C ->Set] -> Interp C
    ObjI (MuI F) = Mu F
    ArrI (MuI F) = mapMu
    idenI (MuI F) = mapIMu
    compI (MuI F) = mapCMu

data Nat : Set where
  _su : Nat -> Nat
  ze : Nat

{-# BUILTIN NATURAL Nat #-}

data _<=_ : Nat -> Nat -> Set where
  _no : forall {n m} -> n <= m -> n <= (m su)
  _su : forall {n m} -> n <= m -> (n su) <= (m su)
  ze  : ze <= ze

iota : forall {n} -> n <= n
iota {n su} = iota {n} su
iota {ze} = ze

_^^_ : forall {p n m} -> p <= n -> n <= m -> p <= m
th ^^ (ph no) = (th ^^ ph) no
(th no) ^^ (ph su) = (th ^^ ph) no
(th su) ^^ (ph su) = (th ^^ ph) su
ze ^^ ze = ze

module _ where
  open SmolCat
  Thin : SmolCat
  Obj Thin = Nat
  Arr Thin = _<=_
  iden Thin = iota
  comp Thin = _^^_
  absl Thin (th no) = _no $~ absl Thin th
  absl Thin (th su) = _su $~ absl Thin th
  absl Thin ze = r~
  absr Thin (ph no) = _no $~ absr Thin ph
  absr Thin (ph su) = _su $~ absr Thin ph
  absr Thin ze = r~
  asso Thin th ph (ps no) = _no $~ asso Thin th ph ps
  asso Thin th (ph no) (ps su) = _no $~ asso Thin th ph ps
  asso Thin (th no) (ph su) (ps su) = _no $~ asso Thin th ph ps
  asso Thin (th su) (ph su) (ps su) = _su $~ asso Thin th ph ps
  asso Thin ze ze ze = r~

  open SmolFun
  SU : SmolFun Thin Thin
  Map SU = _su
  map SU = _su
  mapIden SU = r~
  mapComp SU _ _ = r~

  data Tag : Set where var lam app : Tag

  ULam : Interp Thin
  ULam = MuI (sgm Tag \
    { var -> hom 1
    ; lam -> com SU (rec r~)
    ; app -> prd (rec r~) (rec r~)
    })


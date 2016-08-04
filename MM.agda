module MM where

data _==_ {l}{X : Set l}(x : X) : X -> Set l where
  refl : x == x
{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}

id : {X : Set} -> X -> X
id x = x

data Two : Set where tt ff : Two

record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg
_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T
_+_ : Set -> Set -> Set
S + T = Sg Two \ { tt -> S ; ff -> T}
infixr 4 _,_

inspect : forall {X}(x : X) -> Sg X \ y -> x == y
inspect x = x , refl

record One : Set where
  constructor <>

record _*-*_ {A B C : Set}(R : A -> B -> Set)(S : B -> C -> Set)
            (a : A)(c : C) : Set where
  constructor _,_
  field
    {mid} : B
    left  : R a mid
    right : S mid c
open _*-*_

data Zero : Set where

data Bwd (X : Set) : Set where
  [] : Bwd X
  _-,_ : Bwd X -> X -> Bwd X
infixl 5 _-,_

data _:>_ {X : Set} : Bwd X -> X -> Set where
  ze : forall {xz x} -> (xz -, x) :> x
  su : forall {xz x y} -> xz :> x -> (xz -, y) :> x

infixl 5 _+<+_
_+<+_ : {X : Set} -> Bwd X -> Bwd X -> Bwd X
yz +<+ [] = yz
yz +<+ (xz -, x) = yz +<+ xz -, x

assoc : forall {X} (xz yz zz : Bwd X) ->
  (xz +<+ (yz +<+ zz)) == ((xz +<+ yz) +<+ zz)
assoc xz yz [] = refl
assoc xz yz (zz -, x) rewrite assoc xz yz zz = refl

float : forall {I} jz {iz}{i : I} -> iz :> i -> (jz +<+ iz) :> i
float jz ze = ze
float jz (su x) = su (float jz x)

All : {X : Set} -> (X -> Set) -> Bwd X -> Set
All P [] = One
All P (xz -, x) = All P xz * P x

all : {X : Set}{P Q : X -> Set} -> (forall {x} -> P x -> Q x)
      -> forall xz -> All P xz -> All Q xz
all f [] <> = <>
all f (xz -, x) (pa , p) = all f xz pa , f p

allCat : {X : Set}{P : X -> Set}{xz yz : Bwd X} ->
        All P xz -> All P yz -> All P (xz +<+ yz)
allCat {yz = []} xp yp = xp
allCat {yz = yz -, x} xp (yp , p) = allCat xp yp , p

proj : {X : Set}(P : X -> Set){xz : Bwd X}(pz : All P xz) ->
       {x : X} -> xz :> x -> P x
proj P (pa , p) ze     = p
proj P (pa , p) (su i) = proj P pa i

Arity : (I : Set) -> Set
Arity I = Bwd I * I

data Star {X : Set}(R : X -> X -> Set)(x : X) : X -> Set where
  [] : Star R x x
  _,-_  : forall {y z} -> R x y -> Star R y z -> Star R x z

data Desc (I : Set) : Set where
    tm   : I -> Desc I
    _->'_ : I -> Desc I -> Desc I
    _*'_ _+'_ : (D E : Desc I) -> Desc I
    one' zero'  : Desc I
infixr 7 _->'_
infixr 6 _*'_
infixr 5 _+'_

data Tm {I}(D4 : I -> Desc I)(V : Bwd I -> I -> Set)
                                  (iz : Bwd I)(i : I) : Set

Node : forall {I}(X : Bwd I -> I -> Set)
              (iz : Bwd I)(D : Desc I) -> Set
Node X iz (tm i)        = X iz i
Node X iz (j ->' D)     = Node X (iz -, j) D
Node X iz (D *' E)      = Node X iz D * Node X iz E
Node X iz one'          = One
Node X iz (D +' E)      = Node X iz D + Node X iz E
Node X iz zero'         = Zero

data Tm {I} D4 V iz i where
  #   : V iz i -> Tm D4 V iz i
  <_> : Node (Tm D4 V) iz (D4 i) -> Tm D4 V iz i

Term : forall {I}(D4 : I -> Desc I)(iz : Bwd I)(i : I) -> Set
Term D4 = Tm D4 _:>_

module RSK {I}(D4 : I -> Desc I)(Im : Bwd I -> I -> Set)
  (vaIm : forall {iz i} -> iz :> i -> Im iz i)
  (imTm : forall {iz i} -> Im iz i -> Term D4 iz i)
  (wkIm : forall {iz i j} -> Im iz i -> Im (iz -, j) i)
  where
  Imz : (iz jz : Bwd I) -> Set
  Imz iz jz = All (Im jz) iz
  idi : (iz : Bwd I) -> Imz iz iz
  shift : forall (iz : Bwd I){i} -> All (Im (iz -, i)) iz
  idi [] = <>
  idi (iz -, i) = shift iz , vaIm ze
  shift iz = all wkIm iz (idi iz)
  lift : forall {iz jz} j -> Imz iz jz -> Imz (iz -, j) (jz -, j)
  lift j g = all wkIm _ g , vaIm ze

  act : forall {iz jz} -> Imz iz jz ->
          forall {i} -> Term D4 iz i -> Term D4 jz i
  acts : forall {iz jz} -> Imz iz jz ->
          forall D -> Node (Term D4) iz D -> Node (Term D4) jz D
  act g (# x)    = imTm (proj (Im _) g x)
  act g {i} (< ts >) = < acts g (D4 i) ts >
  acts g (tm i) t = act g t
  acts g (j ->' D) t = acts (lift j g) D t
  acts g (D *' E) (s , t) = acts g D s , acts g E t
  acts g (D +' E) (tt , t) = tt , acts g D t
  acts g (D +' E) (ff , t) = ff , acts g E t
  acts g one' <> = <>
  acts g zero' ()

module REN {I}{D4 : I -> Desc I} = RSK D4 _:>_ id # su
ren = REN.act
wkn : forall {I}{D4 : I -> Desc I}{iz j i} ->
        Term D4 iz i -> Term D4 (iz -, j) i
wkn {_}{D4} = ren (REN.shift {D4 = D4} _)
module SUB {I}{D4 : I -> Desc I} = RSK D4 (Term D4) # id wkn
sub = SUB.act

shunt : forall {I}{D4 : I -> Desc I}
        (jz iz : Bwd I) -> All (_:>_ (jz +<+ iz)) jz
shunt {D4 = D4} jz [] = REN.idi {D4 = D4} jz 
shunt {D4 = D4} jz (iz -, x) = all su _ (shunt {D4 = D4} jz iz)

data I-BTT : Set where term elim : I-BTT

D4-BTT : I-BTT -> Desc I-BTT
D4-BTT term
  =    tm elim                           -- e
  +'   one'                              -- *
  +'   tm term *' elim ->' tm term       -- (x : S) -> T[x]
  +'   elim ->' tm term                  -- \ x -> t[x]
D4-BTT elim
  =    tm term *' tm term                -- t : T
  +'   tm elim *' tm term                -- f s

pattern [_] e    = < tt , e >
pattern Ty       = < ff , tt , <> >
pattern Pi S T   = < ff , ff , tt , S , T >
pattern lam t    = < ff , ff , ff , t >

pattern _::_ t T = < tt , t , T >
pattern _$_ f s  = < ff , f , s >

myElim : Term D4-BTT [] elim
myElim =
  lam (lam ([ (lam ([ # ze $ [ # ze $ [ # (su ze) ] ] ])
              :: Pi (Pi ([ # (su ze) ]) ([ # (su (su ze)) ]))
                ([ # (su (su ze)) ]))
            $ lam ([ # ze ])
            ]))
  :: Pi Ty (Pi [ # ze ] ([ # (su ze) ]))

module CONTRACTIONSCHEME {I}(D4 : I -> Desc I) where
  Pat : (iz : Bwd I)(i : I) -> Set
  Pat = Tm D4 (\ _ _ -> One)

  patSch  : forall {iz i} -> Pat iz i -> Bwd (Arity I)
  patSchs : forall {iz} D -> Node Pat iz D -> Bwd (Arity I)
  patSch {iz}{i} (# <>) = [] -, (iz , i)
  patSch {iz}{i} < ps > = patSchs (D4 i) ps
  patSchs (tm i) p = patSch p
  patSchs {iz}(j ->' D) ps = patSchs {iz -, j} D ps
  patSchs (D *' E) (ps , qs) = patSchs D ps +<+ patSchs E qs
  patSchs (D +' E) (tt , ps) = patSchs D ps
  patSchs (D +' E) (ff , qs) = patSchs E qs
  patSchs one' <> = []
  patSchs zero' ()

  data EVar (nz : Bwd (Arity I))(iz : Bwd I)(i : I) : Set
  Exp : (nz : Bwd (Arity I))(iz : Bwd I)(i : I) -> Set
  Exp nz = Tm D4 (EVar nz)
  data EVar nz iz i where
    #   : iz :> i -> EVar nz iz i
    _!_ : forall {jz} -> nz :> (jz , i) -> All (Exp nz iz) jz ->
            EVar nz iz i

  record ContractionScheme (i : I) : Set where
    constructor _~>_
    field
      lhs      : Pat [] i
      rhs      : Exp (patSch lhs) [] i
  open ContractionScheme
  infixr 5 _~>_

open CONTRACTIONSCHEME
open ContractionScheme


pattern % = # <>

Contractions-BTT : (i : I-BTT) -> Bwd (ContractionScheme D4-BTT i)
Contractions-BTT term = [] -,
  [ % :: % ] ~> # (su ze ! <>)
Contractions-BTT elim = [] -,
  (lam % :: Pi % %) $ %
    ~> # (su (su (su ze)) ! (<> , # (ze ! <>) :: # (su (su ze) ! <>) ))
       :: # (su ze ! (<> , # (ze ! <>) :: # (su (su ze) ! <>)))
data Maybe (X : Set) : Set where
  yes : X -> Maybe X
  no  : Maybe X

_>>=_ : forall {X Y} -> Maybe X -> (X -> Maybe Y) -> Maybe Y
no >>= _ = no
yes x >>= f = f x

_>>==_ : forall {X Y}(m : Maybe X) ->
         ((x : X) -> m == yes x -> Maybe Y) -> Maybe Y
no >>== _ = no
yes x >>== f = f x refl

module MATCH {I}(D4 : I -> Desc I) where

  Env : (jz : Bwd I) -> Bwd (Arity I) -> Set
  Env jz = All {Arity _} \ { (iz , i) -> Term D4 (jz +<+ iz) i } 

  match : forall {iz i} jz ->
          (p : Pat D4 iz i) -> Term D4 (jz +<+ iz) i
          -> Maybe (Env jz (patSch D4 p))
  matches : forall {iz} jz D ->
          (ps : Node (Pat D4) iz D) -> Node (Term D4) (jz +<+ iz) D
            -> Maybe (Env jz (patSchs D4 D ps))

  match jz % t = yes (<> , t)
  match jz < ps > (# x) = no
  match {i = i} jz < ps > < ts > = matches jz (D4 i) ps ts
  matches jz (tm j) p t = match jz p t
  matches jz (j ->' D) ps ts = matches jz D ps ts
  matches jz (D *' E) (ps , qs) (ts , us) =
    matches jz D ps ts >>= \ g ->
    matches jz E qs us >>= \ h ->
    yes (allCat g h)
  matches jz (D +' E) (tt , ps) (tt , ts) = matches jz D ps ts
  matches jz (D +' E) (tt , ps) (ff , ts) = no
  matches jz (D +' E) (ff , ps) (tt , ts) = no
  matches jz (D +' E) (ff , ps) (ff , ts) = matches jz E ps ts
  matches jz one' <> <> = yes <>
  matches jz zero' () _

  {-# NO_TERMINATION_CHECK #-}
  inst : forall {nz iz} jz (g : Env jz nz)
         {i} -> Exp D4 nz iz i -> Term D4 (jz +<+ iz) i
  insts : forall {nz iz} jz (g : Env jz nz)
          D -> Node (Exp D4 nz) iz D -> Node (Term D4) (jz +<+ iz) D

  inst jz g (# (# x)) = # (float jz x)
  inst jz g (# (x ! es)) with all (inst jz g) _ es
  inst {iz = iz} jz g (# (x ! es)) | tz
    = sub (allCat (all # _ (shunt {D4 = D4} jz iz)) tz) (proj _ g x)
  inst jz g {i} < es > = < insts jz g (D4 i) es >
  insts jz g (tm i) e = inst jz g e
  insts jz g (j ->' D) es = insts jz g D es
  insts jz g (D *' E) (ds , es) = insts jz g D ds , insts jz g E es
  insts jz g (D +' E) (tt , ds) = tt , insts jz g D ds
  insts jz g (D +' E) (ff , es) = ff , insts jz g E es
  insts jz g one' <> = <>
  insts jz g zero' ()

  record Contracts 
       (CSz : (i : I) -> Bwd (ContractionScheme D4 i))
       {iz i}(r r' : Term D4 iz i) : Set where
    constructor contracts
    field
      {scheme} : _
      {matching} : _
      which : CSz i :> scheme
      matched : match iz (lhs scheme) r == yes matching
      instantiated : inst iz matching (rhs scheme) == r'

diff : forall {I} -> Desc I -> Desc I
diff (tm x) = one'
diff (j ->' D) = j ->' diff D
diff (D *' E) = diff D *' E +' D *' diff E
diff (D +' E) = diff D +' diff E
diff one' = zero'
diff zero' = zero'

dArity : forall {I T iz}(D : Desc I) -> Node T iz (diff D) -> Arity I
dArity {iz = iz} (tm i) <> = iz , i
dArity (j ->' D) d' = dArity D d'
dArity (D *' E) (tt , d' , e) = dArity D d'
dArity (D *' E) (ff , d , e') = dArity E e'
dArity (D +' E) (tt , d') = dArity D d'
dArity (D +' E) (ff , e') = dArity E e' 
dArity one' ()
dArity zero' ()

plug : forall {I T iz}(D : Desc I)(d' : Node T iz (diff D)) ->
         let a = dArity D d' in T (fst a) (snd a) -> Node T iz D
plug (tm x) <> t = t
plug (j ->' D) d' t = plug D d' t
plug (D *' E) (tt , d' , e) t = plug D d' t , e
plug (D *' E) (ff , d , e') t = d , plug E e' t
plug (D +' E) (tt , d') t = tt , plug D d' t
plug (D +' E) (ff , d') t = ff , plug E d' t
plug one' () t
plug zero' () t

module REDS {I}{D4 : I -> Desc I}
              (CSz : (i : I) -> Bwd (ContractionScheme D4 i)) where
  open MATCH D4
  open Contracts

  Step : Arity I -> Arity I -> Set
  Step (iz , i) a = Sg (Node (Term D4) iz (diff (D4 i))) \ d' ->
                        dArity (D4 i) d' == a

  step : forall {iz i jz j} -> Step (iz , i) (jz , j) ->
         Term D4 jz j -> Term D4 iz i
  step {i = i} (d' , refl) t = < plug (D4 i) d' t >

  steps : forall {iz i jz j} -> Star Step (iz , i) (jz , j) ->
         Term D4 jz j -> Term D4 iz i
  steps [] t = t
  steps (s ,- ss) t = step s (steps ss t)

  data Red {iz i}(r r' : Term D4 iz i) : Set where
    here  : Contracts CSz r r' -> Red r r'
    under : forall {jz j}
              (s : Step (iz , i) (jz , j))
              {t t' : Term D4 jz j} -> Red t t' ->
            r == step s t ->
            r' == step s t' ->
            Red r r'

  data ParRed {iz i} : (r r' : Term D4 iz i) -> Set

  ParReds : forall {iz} D (r r' : Node (Term D4) iz D) -> Set
  ParReds (tm x) r r' = ParRed r r'
  ParReds (j ->' D) r r' = ParReds D r r'
  ParReds (D *' E) (d , e) (d' , e') = ParReds D d d' * ParReds E e e'
  ParReds (D +' E) (tt , r) (tt , r') = ParReds D r r'
  ParReds (D +' E) (tt , r) (ff , r') = Zero
  ParReds (D +' E) (ff , r) (tt , r') = Zero
  ParReds (D +' E) (ff , r) (ff , r') = ParReds E r r'
  ParReds one' r r' = One
  ParReds zero' () r'

  data ParRed {iz} {i} where
    # : (x : iz :> i) -> ParRed (# x) (# x)
    <_> : forall {r r' : Node (Term D4) iz (D4 i)} ->
           ParReds (D4 i) r r' -> ParRed < r > < r' >
    <_>~>_ : forall {r r' : Node (Term D4) iz (D4 i)} ->
             ParReds (D4 i) r r' -> 
             {t : Term D4 iz i} -> Contracts CSz < r' > t ->
            ParRed < r > t

  contract : forall {iz i}(csz : Bwd (ContractionScheme D4 i)) ->
             (forall {c} -> csz :> c -> CSz i :> c) ->
             (r : Term D4 iz i) ->
             Maybe (Sg (Term D4 iz i) \ r' -> Contracts CSz r r')
  contract [] f t = no
  contract (csz -, c) f t with contract csz (\ z -> f (su z)) t
  contract (csz -, c) f t | yes r = yes r
  contract {iz = iz}(csz -, (lhs ~> rhs)) f t | no =
    match iz lhs t >>== \ g q -> 
    yes (inst iz g rhs , contracts (f ze) q refl)

  dev : forall {iz i}(r : Term D4 iz i) ->
          Sg (Term D4 iz i) \ r' -> ParRed r r'
  devs : forall {iz} D (rs : Node (Term D4) iz D) ->
          Sg (Node (Term D4) iz D) \ rs' -> ParReds D rs rs'

  dev (# x) = # x , # x
  dev {i = i} < rs > with devs (D4 i) rs
  dev {i = i} < rs > | rs' , rs'' with contract (CSz i) id < rs' >
  dev < rs > | rs' , rs'' | yes (t' , q') = t' , < rs'' >~> q'
  dev < rs > | rs' , rs'' | no = < rs' > , < rs'' >
  devs (tm j) r = dev r
  devs (j ->' D) rs = devs D rs
  devs (D *' E) (rs , ss) with devs D rs | devs E ss
  devs (D *' E) (rs , ss) | rs' , rs'' | ss' , ss''
    = (rs' , ss') , (rs'' , ss'')
  devs (D +' E) (tt , rs) with devs D rs
  devs (D +' E) (tt , rs) | rs' , rs'' = (tt , rs') , rs''
  devs (D +' E) (ff , rs) with devs E rs
  devs (D +' E) (ff , rs) | rs' , rs'' = (ff , rs') , rs''
  devs one' <> = <> , <>
  devs zero' ()

  EnvRed : forall {nz iz} -> Env iz nz -> Env iz nz -> Set
  EnvRed {[]} <> <> = Zero
  EnvRed {nz -, a} (g , t) (g' , t')
    = (EnvRed g g' * (t == t'))
    + ((g == g') * Red t t' )

  EnvParRed : forall {nz iz} -> Env iz nz -> Env iz nz -> Set
  EnvParRed {[]} <> <> = One
  EnvParRed {nz -, a} (g , t) (g' , t')
    = EnvParRed g g' * ParRed t t'

  Orthogonality : Set
  Orthogonality = forall {iz i jz j}
    (ds : Star Step (iz , i) (jz , j))
    (r : Term D4 jz j){r' t}
    (c : Contracts CSz (steps ds r) t) ->
    Contracts CSz r r' ->
    Sg (Env _ _) \ g' -> EnvRed (matching c) g' *
    (match _ (lhs (scheme c)) (steps ds r') == yes g')


  takahashi : forall {iz i}(s t : Term D4 iz i) ->
              ParRed s t -> ParRed t (fst (dev s))
  takahashis : forall {iz} D (ss ts : Node (Term D4) iz D) ->
              ParReds D ss ts -> ParReds D ts (fst (devs D ss))
  takahashi .(# x) .(# x) (# x) = # x
  takahashi {i = i} ._ ._ < ps > with takahashis (D4 i) _ _ ps
  takahashi {i = i} ._ ._ (<_> {r = ss}{r' = ts} ps) | qs with devs (D4 i) ss
  takahashi ._ ._ < ps > | qs | us , rs with contract (CSz _) id < us >
  takahashi ._ ._ < ps > | qs | us , rs | yes (v , q) = < qs >~> q
  takahashi ._ ._ < ps > | qs | us , rs | no = < qs >
  takahashi {i = i} ._ t (< ps >~> c) with takahashis (D4 i) _ _ ps
  takahashi ._ t (< ps >~> MATCH.contracts which matched instantiated) | qs = {!!}
  takahashis (tm j) ss ts ps = takahashi ss ts ps
  takahashis (j ->' D) ss ts ps = takahashis D ss ts ps
  takahashis (D *' E) (ss , ss') (ts , ts') (ps , ps')
    = takahashis D ss ts ps , takahashis E ss' ts' ps'
  takahashis (D +' E) (tt , ss) (tt , ts) ps = takahashis D ss ts ps
  takahashis (D +' E) (tt , ss) (ff , ts) ()
  takahashis (D +' E) (ff , ss) (tt , ts) ()
  takahashis (D +' E) (ff , ss) (ff , ts) ps = takahashis E ss ts ps
  takahashis one' ss ts <> = <>
  takahashis zero' ()

open REDS

dev-BTT = dev Contractions-BTT
ex1 = dev-BTT myElim
ex2 = dev-BTT (fst ex1)
ex3 = dev-BTT (fst ex2)
ex4 = dev-BTT (fst ex3)


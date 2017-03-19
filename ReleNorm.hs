{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeFamilies,
    RankNTypes, PolyKinds, FlexibleInstances, FlexibleContexts,
    MultiParamTypeClasses, StandaloneDeriving,
    ScopedTypeVariables #-}

module ReleNorm where

{-----------------------------------------------------------------------------
This file contains an implementation of relevant normalization for untyped
lambda terms.

A relevant normal form is a normal form which uses all free variables at
least once. Relevant normal forms must thus distinguish constant functions
from functions which use their argument (i.e., relevant functions), as
well as ensuring an absence of beta redexes.

Relevant normalization of an open term over an input scope
computes (partially, natch)
its relevant normal form over some output scope
and the embedding of the output scope into the input scope.
-----------------------------------------------------------------------------}


------------------------------------------------------------------------------
-- NATURAL NUMBERS
------------------------------------------------------------------------------

-- usual type level numbers and singletons
data Nat = Z | S Nat deriving Show

-- working with Nat-indexed things, we'll sometimes need to know "all Show"
class ShowN (f :: Nat -> *) where
  showN :: f n -> String


------------------------------------------------------------------------------
-- LAMBDA CALCULUS
------------------------------------------------------------------------------

-- Yer traditional well scoped lambda terms with de Bruijn indices
data Tm :: Nat -> * where
  V     :: Fin n -> Tm n            -- for Fin, see below
  (:$)  :: Tm n -> Tm n -> Tm n
  L     :: Tm (S n) -> Tm n
deriving instance Show (Tm n)
instance ShowN Tm where showN = show


------------------------------------------------------------------------------
-- ORDER PRESERVING EMBEDDINGS
------------------------------------------------------------------------------

data OPE :: Nat -> Nat -> * where
  OPEI :: OPE n n                     -- convenient redundancy
  OPES :: OPE n m -> OPE (S n) (S m)  -- OPES OPEI ~ OPEI
  OPEN :: OPE Z m                     -- OPEN Zy ~ OPEI Zy
  OPE' :: OPE n m -> OPE n (S m)      -- OPE' OPEN ~ OPEN
instance Show (OPE n m) where
  show OPEI     = "I"
  show (OPES p) = show p ++ "|"
  show OPEN     = "0"
  show (OPE' p) = show p ++ "'"
instance ShowN (OPE n) where showN = show

-- smart constructors maximizing use of OPEI and OPEN
opeS :: OPE n m -> OPE (S n) (S m)
opeS OPEI = OPEI
opeS p    = OPES p

ope' :: OPE n m -> OPE n (S m)
ope' OPEN = OPEN
ope' p    = OPE' p

-- smart eliminators for OPEs
ope2Z :: OPE n Z -> (n ~ Z => t) -> t
ope2Z OPEI t = t
ope2Z OPEN t = t

ope2S :: (OPE n' m -> t) ->
         (forall n. n' ~ S n => OPE n m -> t) ->
         OPE n' (S m) -> t
ope2S f' fS (OPES p) = fS p
ope2S f' fS  OPEI    = fS OPEI
ope2S f' fS (OPE' p) = f' p
ope2S f' fS  OPEN    = f' OPEN

opeS2 :: (forall m. m' ~ S m => OPE (S n) (S m) -> t) ->
         OPE (S n) m' -> t
opeS2 f  OPEI    = f OPEI
opeS2 f (OPES p) = f (OPES p)
opeS2 f (OPE' p) = f (OPE' p)
         
-- composition of OPEs
(<^>) :: OPE m p -> OPE n m -> OPE n p
p      <^> OPEN   = OPEN
OPEI   <^> q      = q
p      <^> OPEI   = p
OPES p <^> OPES q = opeS (p <^> q)
OPES p <^> OPE' q = ope' (p <^> q)
OPE' p <^> q      = ope' (p <^> q)
infixl 6 <^>

-- Finite sets are OPEs from one
type Fin = OPE (S Z)

fZ :: Fin (S n)
fZ = opeS OPEN

fS :: Fin n -> Fin (S n)
fS = ope'

-- value-preserving embedding
fE :: Fin n -> Fin (S n)
fE = opeS2 (ope2S (ope' . fE) (opeS . ope'))


------------------------------------------------------------------------------
-- THINNED THINGS
------------------------------------------------------------------------------

-- A thinned f is an f over only some of the variables in scope.
data Th :: (Nat -> *) -> Nat -> * where
  (:<) :: f n -> OPE n m -> Th f m
infixr 4 :<

-- We like thinned relevant things a lot, as it standardises where thinning
-- happens.

-- Of course, thinned things are functorial in the things (and in the
-- thinnings, but that's another story).
(^$) :: (forall n. f n -> g n) -> Th f n -> Th g n
h ^$ (f :< u) = h f :< u


------------------------------------------------------------------------------
-- OPE COPRODUCTS AND RELEVANT PAIRS
------------------------------------------------------------------------------

-- Encoding pairs of OPEs with the same target,
-- ensuring that the target is *covered*.

data OPE2 :: Nat -> Nat -> Nat -> * where
  OPEII :: OPE2 m m m  -- OPESS OPEII ~ OPEII   OPEII{Z} ~ OPENI{Z} ~ OPEIN{Z}
  OPENI :: OPE2 Z m m  -- OPE'S OPENI ~ OPENI
  OPEIN :: OPE2 m Z m  -- OPES' OPEIN ~ OPEIN
  OPESS :: OPE2 n n' m -> OPE2 (S n) (S n') (S m)
  OPES' :: OPE2 n n' m -> OPE2 (S n) n' (S m)
  OPE'S :: OPE2 n n' m -> OPE2 n (S n') (S m)
instance Show (OPE2 n n' m) where
  show OPEII = "II"
  show OPENI = "0I"
  show OPEIN = "I0"
  show (OPESS p) = show p ++ "^"
  show (OPES' p) = show p ++ "/"
  show (OPE'S p) = show p ++ "\\"

-- relevant pairs
data RP :: (Nat -> *) -> (Nat -> *) -> (Nat -> *) where
  RP :: f n -> OPE2 n n' m -> g n' -> RP f g m
instance (ShowN f, ShowN g) => Show (RP f g m) where
  show (RP f p g) = "(" ++ showN f ++ " <" ++ show p ++ "> " ++ showN g ++ ")"
instance (ShowN f, ShowN g) => ShowN (RP f g) where showN = show
(<&>) :: (forall n. f n -> f' n) -> (forall n. g n -> g' n) ->
         RP f g n -> RP f' g' n
(ff <&> gg) (RP f p g) = RP (ff f) p (gg g)

-- OPEII is redundant: we really need only
opeZZ :: OPE2 Z Z Z
opeZZ = OPEII -- Zy

-- smart constructors, ya da ya da
opeSS :: OPE2 n n' m -> OPE2 (S n) (S n') (S m)
opeSS OPEII = OPEII
opeSS p     = OPESS p

opeS' :: OPE2 n n' m -> OPE2 (S n) n' (S m)
opeS' OPEIN = OPEIN
opeS' p     = OPES' p

ope'S :: OPE2 n n' m -> OPE2 n (S n') (S m)
ope'S OPENI = OPENI
ope'S p     = OPE'S p

-- extract left OPE
lope :: OPE2 n n' m -> OPE n m
lope OPEII     = OPEI
lope OPEIN     = OPEI
lope OPENI     = OPEN
lope (OPESS p) = opeS (lope p)
lope (OPES' p) = opeS (lope p)
lope (OPE'S p) = ope' (lope p)

-- extract right OPE
rope :: OPE2 n n' m -> OPE n' m
rope OPEII     = OPEI
rope OPENI     = OPEI
rope OPEIN     = OPEN
rope (OPESS p) = opeS (rope p)
rope (OPE'S p) = opeS (rope p)
rope (OPES' p) = ope' (rope p)

-- construct an OPE2 by growing its left OPE
opel :: OPE n m -> OPE2 n m m
opel  OPEI    = OPEII
opel  OPEN    = OPENI
opel (OPES p) = opeSS (opel p)
opel (OPE' p) = ope'S (opel p)

-- construct an OPE2 by growing its right OPE
oper :: OPE n m -> OPE2 m n m
oper  OPEI    = OPEII
oper  OPEN    = OPEIN
oper (OPES p) = opeSS (oper p)
oper (OPE' p) = opeS' (oper p)

-- if you have two OPEs targeting m', then we can compute the
-- OPE2 which targets the union of their images, and the OPE which
-- embeds *that* in m' (representing the points hit by neither);
-- it's a kind of coproduct calculation, being the smallest thing
-- supporting both injections

data COP :: Nat -> Nat -> Nat -> * where
  COP :: OPE2 n n' m -> OPE m m' -> COP n n' m'
cop :: OPE n m' -> OPE n' m' -> COP n n' m'
cop  OPEI          q  = COP (oper q) OPEI
cop       p   OPEI    = COP (opel p) OPEI
cop  OPEN          q  = COP OPENI q
cop       p   OPEN    = COP OPEIN p
cop (OPES p) (OPES q) = case cop p q of COP pq r -> COP (opeSS pq) (opeS r)
cop (OPES p) (OPE' q) = case cop p q of COP pq r -> COP (opeS' pq) (opeS r)
cop (OPE' p) (OPES q) = case cop p q of COP pq r -> COP (ope'S pq) (opeS r)
cop (OPE' p) (OPE' q) = case cop p q of COP pq r -> COP pq         (ope' r)

-- Correspondingly, we get the following smart constructor
-- making thinned relevant pairs from thinned things.

rp :: Th f m -> Th g m -> Th (RP f g) m
rp (f :< u) (g :< v) = case cop u v of COP p w -> RP f p g :< w


------------------------------------------------------------------------------
-- RELEVANT ASSOCIAION
------------------------------------------------------------------------------

rassocLR :: RP (RP f g) h n -> RP f (RP g h) n
rassocLR (RP (RP f p g) q h) = case ope2ASSOC p q of
  OPE2ASSOC s r -> RP f r (RP g s h)

data OPE2ASSOC :: Nat -> Nat -> Nat -> Nat -> Nat -> * where
  OPE2ASSOC :: OPE2 l m lm -> OPE2 k lm klm
            -> OPE2ASSOC k l kl m klm

ope2ASSOC :: OPE2 k l kl -> OPE2 kl m klm -> OPE2ASSOC k l kl m klm
ope2ASSOC OPEII q     = OPE2ASSOC q (opel (lope q))
ope2ASSOC OPENI q     = OPE2ASSOC q OPENI
ope2ASSOC OPEIN q     = OPE2ASSOC OPENI q
ope2ASSOC p OPEII     = OPE2ASSOC (opel (rope p)) (opel (lope p))
ope2ASSOC p OPEIN     = OPE2ASSOC OPEIN p
-- ope2ASSOC p OPENI is covered
ope2ASSOC p (OPE'S q) = case ope2ASSOC p q of
  OPE2ASSOC r s -> OPE2ASSOC (ope'S r) (ope'S s)
ope2ASSOC (OPESS p) (OPES' q) = case ope2ASSOC p q of
  OPE2ASSOC r s -> OPE2ASSOC (opeS' r) (opeSS s)
ope2ASSOC (OPE'S p) (OPES' q) = case ope2ASSOC p q of
  OPE2ASSOC r s -> OPE2ASSOC (opeS' r) (ope'S s)
ope2ASSOC (OPES' p) (OPES' q) = case ope2ASSOC p q of
  OPE2ASSOC r s -> OPE2ASSOC r (opeS' s)
ope2ASSOC (OPESS p) (OPESS q) = case ope2ASSOC p q of
  OPE2ASSOC r s -> OPE2ASSOC (opeSS r) (opeSS s)
ope2ASSOC (OPE'S p) (OPESS q) = case ope2ASSOC p q of
  OPE2ASSOC r s -> OPE2ASSOC (opeSS r) (ope'S s)
ope2ASSOC (OPES' p) (OPESS q) = case ope2ASSOC p q of
  OPE2ASSOC r s -> OPE2ASSOC (ope'S r) (opeSS s)

-- managed to avoid using this, but didn't want to throw it away!


------------------------------------------------------------------------------
-- RELEVANT NORMAL FORMS
------------------------------------------------------------------------------

-- normal terms are abstractions or applications of a var to a spine
data Nm :: Nat -> * where
  NK :: Nm m      -> Nm m
  NL :: Nm (S m)  -> Nm m
  NE :: Ne m      -> Nm m
deriving instance Show (Nm n)
instance ShowN Nm where showN = show

-- neutrals are left-nested applications of variables
data Ne :: Nat -> * where
  NV :: Ne (S Z)
  NA :: RP Ne Nm m -> Ne m
deriving instance Show (Ne n)
instance ShowN Ne where showN = show

-- reassociation of OPE2s


------------------------------------------------------------------------------
-- SELECTIONS
------------------------------------------------------------------------------

-- This may seem like an obfuscated predecessor relation, but only because
-- natural numbers are so confusing. On lists, it would be the deletion
-- relation...

data Sel :: Nat -> Nat -> * where
  Zs :: Sel (S n) n
  Ss :: Sel m n -> Sel (S m) (S n)

-- ...and besides, there's info in the inhabitant

-- When a Sel and an OPE2 interact, something hits something.

data Which :: Nat -> Nat -> Nat -> * where
  Hit0 :: Sel n0' n0               -> OPE2 n0 n1' m -> Which n0' n1' m
  Hit1 ::               Sel n1' n1 -> OPE2 n0' n1 m -> Which n0' n1' m
  Hit2 :: Sel n0' n0 -> Sel n1' n1 -> OPE2 n0  n1 m -> Which n0' n1' m

which :: Sel m' m -> OPE2 n0' n1' m' -> Which n0' n1' m
which x  OPEII     = Hit2 x  x  OPEII
which x  OPEIN     = Hit0 x     OPEIN
which x  OPENI     = Hit1    x  OPENI
which Zs (OPES' p) = Hit0 Zs    p
which Zs (OPE'S p) = Hit1    Zs p
which Zs (OPESS p) = Hit2 Zs Zs p
which (Ss x) (OPESS p) = case which x p of
  Hit0 y   q -> Hit0 (Ss y)        (opeSS q)
  Hit1   z q -> Hit1        (Ss z) (opeSS q)
  Hit2 y z q -> Hit2 (Ss y) (Ss z) (opeSS q)
which (Ss x) (OPES' p) = case which x p of
  Hit0 y   q -> Hit0 (Ss y)        (opeS' q)
  Hit1   z q -> Hit1            z  (opeS' q)
  Hit2 y z q -> Hit2 (Ss y)     z  (opeS' q)
which (Ss x) (OPE'S p) = case which x p of
  Hit0 y   q -> Hit0     y         (ope'S q)
  Hit1   z q -> Hit1        (Ss z) (ope'S q)
  Hit2 y z q -> Hit2     y  (Ss z) (ope'S q)


------------------------------------------------------------------------------
-- HEREDITARY SUBSTITUTION
------------------------------------------------------------------------------

nsub :: Th (Sel m') m -> Nm m' -> Th Nm m -> Th Nm m
nsub x        (NK t)  s       = NK ^$ nsub x t s
nsub (x :< p) (NL t) (s :< u) = abst $ nsub (Ss x :< OPES p) t (s :< OPE' u)
nsub x        (NE t)  s       = hsub x t s

abst :: Th Nm (S m) -> Th Nm m
abst (t :< w) = ope2S (NK t :<) (NL t :<) w

hsub :: Th (Sel n') m -> Ne n' -> Th Nm m -> Th Nm m
hsub _        NV              s = s
hsub (x :< p) (NA (RP f q a)) s = apply $ case which x q of
  Hit0 y   r -> (hsub (y :< p <^> lope r) f s , a :< p <^> rope r)
  Hit1   z r -> (NE f :< p <^> lope r         , nsub (z :< p <^> rope r) a s)
  Hit2 y z r -> (hsub (y :< p <^> lope r) f s , nsub (z :< p <^> rope r) a s)

apply :: (Th Nm m, Th Nm m) -> Th Nm m
apply (NK t :< u, _) = t :< u
apply (NL t :< u, s) = nsub (Zs :< u) t s
apply (NE f :< u, s) = (NE . NA) ^$ rp (f :< u) s


------------------------------------------------------------------------------
-- NORMALIZATION
------------------------------------------------------------------------------

nm :: Tm n -> Th Nm n
nm (V i)    = NE NV :< i
nm (L t)    = abst (nm t)
nm (f :$ s) = apply (nm f, nm s)

instance ShowN f => Show (Th f n) where
  show (f :< w) = showN f ++ " :< " ++ show w
instance ShowN f => ShowN (Th f) where
  showN = show


------------------------------------------------------------------------------
-- THE JIGGER
------------------------------------------------------------------------------

class LE n m where
  embed :: OPE n m

instance LE Z Z where
  embed = OPEI

instance LE Z m => LE Z (S m) where
  embed = OPE' embed

instance LE n m => LE (S n) (S m) where
  embed = case (embed :: OPE n m) of
    OPEI   -> OPEI
    OPE' p -> OPE' (jig p)

jig :: OPE n m -> OPE (S n) (S m)
jig OPEI     = OPEI
jig (OPE' p) = OPE' (jig p)

la :: forall n. ((forall m. LE (S n) m => Tm m) -> Tm (S n))
   -> Tm n
la f = L (f (V (embed <^> (fZ :: Fin (S n)))))

cl :: Tm Z -> Tm Z
cl = id


------------------------------------------------------------------------------
-- AMEN
------------------------------------------------------------------------------

add :: Tm Z
add = la$ \m -> la$ \n -> la$ \f -> la$ \x -> m :$ f :$ (n :$ f :$ x)

mult :: Tm Z
mult = la$ \m -> la$ \n -> la$ \f -> m :$ (n :$ f)

expo :: Tm Z
expo = la$ \m -> la$ \n -> n :$ m

naught :: Tm Z
naught = la$ \ f -> la$ \ x -> x

one = expo :$ naught :$ naught
two = add :$ one :$ one
four = mult :$ two :$ two
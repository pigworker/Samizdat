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
data Natty :: Nat -> * where
  Zy :: Natty Z
  Sy :: Natty n -> Natty (S n)
class NATTY (n :: Nat) where
  natty :: Natty n
instance NATTY Z where
  natty = Zy
instance NATTY n => NATTY (S n) where
  natty = Sy natty

-- working with Nat-indexed things, we'll sometimes need to know "all Show"
class ShowN (f :: Nat -> *) where
  showN :: f n -> String
instance ShowN Natty where showN = show

nat :: Natty n -> Int
nat Zy     = 0
nat (Sy m) = 1 + nat m
instance Show (Natty n) where
  show = show . nat


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
  OPEI :: Natty n -> OPE n n          -- convenient redundancy
  OPES :: OPE n m -> OPE (S n) (S m)  -- OPES (OPEI n) ~ OPEI (Sy n)
  OPE' :: OPE n m -> OPE n (S m)
instance Show (OPE n m) where
  show (OPEI n) = show n
  show (OPES p) = show p ++ "|"
  show (OPE' p) = show p ++ "'"
instance ShowN (OPE n) where showN = show

-- smart constructor maximizing use of OPEI
opeS :: OPE n m -> OPE (S n) (S m)
opeS (OPEI n) = OPEI (Sy n)
opeS p        = OPES p

-- finding both ends of an OPE
opeEnds :: OPE n m -> (Natty n, Natty m)
opeEnds (OPEI n) = (n, n)
opeEnds (OPES p) = case opeEnds p of
  (n, m) -> (Sy n, Sy m)
opeEnds (OPE' p) = case opeEnds p of
  (n, m) -> (n, Sy m)

-- composition of OPEs
(<^>) :: OPE m p -> OPE n m -> OPE n p
OPEI _ <^> q      = q
p      <^> OPEI _ = p
OPES p <^> OPES q = opeS (p <^> q)
OPES p <^> OPE' q = OPE' (p <^> q)
OPE' p <^> q      = OPE' (p <^> q)
infixl 6 <^>

-- OPEs from empty
nOPE :: Natty n -> OPE Z n
nOPE Zy     = OPEI Zy
nOPE (Sy n) = OPE' (nOPE n)

-- Finite sets are OPEs from one
type Fin = OPE (S Z)

fZ :: NATTY n => Fin (S n)
fZ = opeS (nOPE natty)

fS :: Fin n -> Fin (S n)
fS = OPE'

-- value-preserving embedding
fE :: Fin n -> Fin (S n)
fE (OPEI (Sy Zy)) = fE (OPES (OPEI Zy))
fE (OPES p) = opeS (nOPE (Sy (snd (opeEnds p))))
fE (OPE' p) = OPE' (fE p)


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
  OPEII :: Natty m -> OPE2 m m m
  OPESS :: OPE2 n n' m -> OPE2 (S n) (S n') (S m)
  OPES' :: OPE2 n n' m -> OPE2 (S n) n' (S m)
  OPE'S :: OPE2 n n' m -> OPE2 n (S n') (S m)
instance Show (OPE2 n n' m) where
  show (OPEII n) = show n
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
opeZZ = OPEII Zy

-- smart constructor, ya da ya da
opeSS :: OPE2 n n' m -> OPE2 (S n) (S n') (S m)
opeSS (OPEII n) = OPEII (Sy n)
opeSS p         = OPESS p

-- extract left OPE
lope :: OPE2 n n' m -> OPE n m
lope (OPEII n) = OPEI n
lope (OPESS p) = opeS (lope p)
lope (OPES' p) = opeS (lope p)
lope (OPE'S p) = OPE' (lope p)

-- extract right OPE
rope :: OPE2 n n' m -> OPE n' m
rope (OPEII n) = OPEI n
rope (OPESS p) = opeS (rope p)
rope (OPES' p) = OPE' (rope p)
rope (OPE'S p) = opeS (rope p)

-- extract doms and cod

ope2Ends :: OPE2 n n' m -> (Natty n, Natty n', Natty m)
ope2Ends (OPEII m) = (m, m, m)
ope2Ends (OPESS p) = case ope2Ends p of (n, n', m) -> (Sy n, Sy n', Sy m)
ope2Ends (OPES' p) = case ope2Ends p of (n, n', m) -> (Sy n,    n', Sy m)
ope2Ends (OPE'S p) = case ope2Ends p of (n, n', m) -> (   n, Sy n', Sy m)

-- construct an OPE2 by growing its left OPE
opel :: OPE n m -> OPE2 n m m
opel (OPEI n) = OPEII n
opel (OPES p) = opeSS (opel p)
opel (OPE' p) = OPE'S (opel p)

-- construct an OPE2 by growing its right OPE
oper :: OPE n m -> OPE2 m n m
oper (OPEI n) = OPEII n
oper (OPES p) = opeSS (oper p)
oper (OPE' p) = OPES' (oper p)

-- if you have two OPEs targeting m', then we can compute the
-- OPE2 which targets the union of their images, and the OPE which
-- embeds *that* in m' (representing the points hit by neither);
-- it's a kind of coproduct calculation, being the smallest thing
-- supporting both injections

data COPOPE :: Nat -> Nat -> Nat -> * where
  COPOPE :: OPE2 n n' m -> OPE m m' -> COPOPE n n' m'
copOPE :: OPE n m' -> OPE n' m' -> COPOPE n n' m'
copOPE (OPEI n) (OPEI _) = COPOPE (OPEII n)   (OPEI n)
copOPE (OPEI (Sy n))   q = copOPE (OPES (OPEI n)) q
copOPE p   (OPEI (Sy n)) = copOPE p (OPES (OPEI n))
copOPE (OPES p) (OPES q) = case copOPE p q of
  COPOPE pq r -> COPOPE (opeSS pq) (opeS r)
copOPE (OPES p) (OPE' q) = case copOPE p q of
  COPOPE pq r -> COPOPE (OPES' pq) (opeS r)
copOPE (OPE' p) (OPES q) = case copOPE p q of
  COPOPE pq r -> COPOPE (OPE'S pq) (opeS r)
copOPE (OPE' p) (OPE' q) = case copOPE p q of
  COPOPE pq r -> COPOPE pq (OPE' r)

-- Correspondingly, we get the following smart constructor
-- making thinned relevant pairs from thinned things.

rp :: Th f m -> Th g m -> Th (RP f g) m
rp (f :< u) (g :< v) = case copOPE u v of
  COPOPE p w -> RP f p g :< w


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
ope2ASSOC (OPEII (Sy k)) q = ope2ASSOC (OPESS (OPEII k)) q
ope2ASSOC p (OPEII (Sy m)) = ope2ASSOC p (OPESS (OPEII m))
ope2ASSOC (OPEII Zy) (OPEII Zy) = OPE2ASSOC opeZZ opeZZ
ope2ASSOC p (OPE'S q) = case ope2ASSOC p q of
  OPE2ASSOC r s -> OPE2ASSOC (OPE'S r) (OPE'S s)
ope2ASSOC (OPESS p) (OPES' q) = case ope2ASSOC p q of
  OPE2ASSOC r s -> OPE2ASSOC (OPES' r) (opeSS s)
ope2ASSOC (OPE'S p) (OPES' q) = case ope2ASSOC p q of
  OPE2ASSOC r s -> OPE2ASSOC (OPES' r) (OPE'S s)
ope2ASSOC (OPES' p) (OPES' q) = case ope2ASSOC p q of
  OPE2ASSOC r s -> OPE2ASSOC r (OPES' s)
ope2ASSOC (OPESS p) (OPESS q) = case ope2ASSOC p q of
  OPE2ASSOC r s -> OPE2ASSOC (opeSS r) (opeSS s)
ope2ASSOC (OPE'S p) (OPESS q) = case ope2ASSOC p q of
  OPE2ASSOC r s -> OPE2ASSOC (opeSS r) (OPE'S s)
ope2ASSOC (OPES' p) (OPESS q) = case ope2ASSOC p q of
  OPE2ASSOC r s -> OPE2ASSOC (OPE'S r) (opeSS s)

-- managed to avoid using this, but didn't want to throw it away!


------------------------------------------------------------------------------
-- RELEVANT NORMAL FORMS
------------------------------------------------------------------------------

-- normal terms are abstractions or applications of a var to a spine
data Nm :: Nat -> * where
  NK :: Nm m -> Nm m
  NL :: Nm (S m) -> Nm m
  NE :: Ne m -> Nm m
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
  Zs :: Natty n -> Sel (S n) n
  Ss :: Sel m n -> Sel (S m) (S n)

-- ...and besides, there's info in the inhabitant

selOPE2 :: Sel m n -> OPE2 (S Z) n m
selOPE2 (Zs n) = OPES' (opel (nOPE n))
selOPE2 (Ss x) = OPE'S (selOPE2 x)

selDom :: Sel m n -> Natty n
selDom (Zs n) = n
selDom (Ss x) = Sy (selDom x)

-- When a Sel and an OPE2 interact, something hits something.

data Which :: Nat -> Nat -> Nat -> * where
  Hit0 :: Sel n0' n0               -> OPE2 n0 n1' m -> Which n0' n1' m
  Hit1 ::               Sel n1' n1 -> OPE2 n0' n1 m -> Which n0' n1' m
  Hit2 :: Sel n0' n0 -> Sel n1' n1 -> OPE2 n0  n1 m -> Which n0' n1' m

which :: Sel m' m -> OPE2 n0' n1' m' -> Which n0' n1' m
which x (OPEII (Sy m)) = which x (OPESS (OPEII m))
which (Zs m) (OPES' p) = case ope2Ends p of
  (n0, n1, _) -> Hit0 (Zs n0)         p
which (Zs m) (OPE'S p) = case ope2Ends p of
  (n0, n1, _) -> Hit1         (Zs n1) p
which (Zs m) (OPESS p) = case ope2Ends p of
  (n0, n1, _) -> Hit2 (Zs n0) (Zs n1) p
which (Ss x) (OPESS p) = case which x p of
  Hit0 y   q -> Hit0 (Ss y)        (opeSS q)
  Hit1   z q -> Hit1        (Ss z) (opeSS q)
  Hit2 y z q -> Hit2 (Ss y) (Ss z) (opeSS q)
which (Ss x) (OPES' p) = case which x p of
  Hit0 y   q -> Hit0 (Ss y)        (OPES' q)
  Hit1   z q -> Hit1            z  (OPES' q)
  Hit2 y z q -> Hit2 (Ss y)     z  (OPES' q)
which (Ss x) (OPE'S p) = case which x p of
  Hit0 y   q -> Hit0     y         (OPE'S q)
  Hit1   z q -> Hit1        (Ss z) (OPE'S q)
  Hit2 y z q -> Hit2     y  (Ss z) (OPE'S q)


------------------------------------------------------------------------------
-- HEREDITARY SUBSTITUTION
------------------------------------------------------------------------------

nsub :: Th (Sel m') m -> Nm m' -> Th Nm m -> Th Nm m
nsub x        (NK t)  s       = NK ^$ nsub x t s
nsub (x :< p) (NL t) (s :< u) = abst $ nsub (Ss x :< OPES p) t (s :< OPE' u)
nsub x        (NE t)  s       = hsub x t s

abst :: Th Nm (S m) -> Th Nm m
abst (t :< OPE' w)      = NK t :< w
abst (t :< OPES w)      = NL t :< w
abst (t :< OPEI (Sy m)) = NL t :< OPEI m

hsub :: Th (Sel n') m -> Ne n' -> Th Nm m -> Th Nm m
hsub _        NV              s = s
hsub (x :< p) (NA (RP f q a)) s = apply $ case which x q of
  Hit0 y   r -> (hsub (y :< p <^> lope r) f s , a :< p <^> rope r)
  Hit1   z r -> (NE f :< p <^> lope r         , nsub (z :< p <^> rope r) a s)
  Hit2 y z r -> (hsub (y :< p <^> lope r) f s , nsub (z :< p <^> rope r) a s)

apply :: (Th Nm m, Th Nm m) -> Th Nm m
apply (NK t :< u, _) = t :< u
apply (NL t :< u, s) = nsub (Zs (fst (opeEnds u)) :< u) t s
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

class LT n m where
  theVar :: Natty n -> Fin m

instance LT Z (S Z) where
  theVar Zy = OPEI (Sy Zy)

instance LT Z (S m) => LT Z (S (S m)) where
  theVar Zy = OPE' (theVar Zy)

instance LT n m => LT (S n) (S m) where
  theVar (Sy n) = fE (theVar n)

la :: forall n. NATTY n =>
      ((forall m. LT n m => Tm m) -> Tm (S n))
   -> Tm n
la f = L (f (V (theVar (natty :: Natty n))))

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

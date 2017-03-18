{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving, TypeFamilies,
    UndecidableInstances, RankNTypes #-}

module Relevant where

--------------------------------------------------------------------------
-- NATURAL NUMBERS
--------------------------------------------------------------------------

-- usual type level numbers and singletons
data Nat = Z | S Nat deriving Show
data Natty :: Nat -> * where
  Zy :: Natty Z
  Sy :: Natty n -> Natty (S n)
deriving instance Show (Natty n)
class NATTY (n :: Nat) where
  natty :: Natty n
instance NATTY Z where
  natty = Zy
instance NATTY n => NATTY (S n) where
  natty = Sy natty


--------------------------------------------------------------------------
-- ORDER PRESERVING EMBEDDINGS
--------------------------------------------------------------------------

-- order preserving embeddings
data OPE :: Nat -> Nat -> * where
  OPEI :: Natty n -> OPE n n
  OPES :: OPE n m -> OPE (S n) (S m)
  OPE' :: OPE n m -> OPE n (S m)
deriving instance Show (OPE n m)

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

-- OPEs from empty
nOPE :: Natty n -> OPE Z n
nOPE Zy     = OPEI Zy
nOPE (Sy n) = OPE' (nOPE n)


--------------------------------------------------------------------------
-- LAMBDA CALCULUS
--------------------------------------------------------------------------

-- Finite sets are OPEs from one
type Fin = OPE (S Z)
fZ :: NATTY n => Fin (S n)
fZ = opeS (nOPE natty)
fS :: Fin n -> Fin (S n)
fS = OPE'

-- Yer traditional well scoped lambda terms
data Tm :: Nat -> * where
  V :: Fin n -> Tm n
  (:$) :: Tm n -> Tm n -> Tm n
  L :: Tm (S n) -> Tm n
deriving instance Show (Tm n)


--------------------------------------------------------------------------
-- OPE COPRODUCTS
--------------------------------------------------------------------------

-- Encoding pairs of OPEs with the same target,
-- ensuring that the target is *covered*.
data OPE2 :: Nat -> Nat -> Nat -> * where
  OPEII :: Natty m -> OPE2 m m m
  OPESS :: OPE2 n n' m -> OPE2 (S n) (S n') (S m)
  OPES' :: OPE2 n n' m -> OPE2 (S n) n' (S m)
  OPE'S :: OPE2 n n' m -> OPE2 n (S n') (S m)
deriving instance Show (OPE2 n n' m)

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

-- construct OPE2 full on left, empty on right
alll :: Natty n -> OPE2 n Z n
alll Zy     = OPEII Zy
alll (Sy n) = OPES' (alll n)

-- construct OPE2 empty on left, full on right
allr :: Natty n -> OPE2 Z n n
allr Zy     = OPEII Zy
allr (Sy n) = OPE'S (allr n)

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

-- annoying lemma: if the sources of an OPE2 are nonzero,
-- the target certainly is
data OPE2SSS :: Nat -> Nat -> Nat -> * where
  OPE2SSS :: OPE2 (S n) (S n') (S m) -> OPE2SSS (S n) (S n') (S m)
ope2SSS :: OPE2 (S n) (S n') m -> OPE2SSS (S n) (S n') m
ope2SSS (OPEII n) = OPE2SSS (OPEII n)
ope2SSS (OPESS p) = OPE2SSS (opeSS p)
ope2SSS (OPES' p) = OPE2SSS (OPES' p)
ope2SSS (OPE'S p) = OPE2SSS (OPE'S p)


--------------------------------------------------------------------------
-- UNDERGROUND RELEVANT TERMS
--------------------------------------------------------------------------

-- closed terms
data Cl :: * where
  (:$$) :: Cl -> Cl -> Cl
  CL :: Un (S Z) -> Cl
  CK :: Cl -> Cl
deriving instance Show Cl

-- stations are either variables or junctions with action in both branches
data St :: Nat -> * where
  It :: St (S Z)
  Ap :: OPE2 (S n) (S n') (S m) -> Un (S n) -> Un (S n') -> St (S m)
deriving instance Show (St n)

-- tubes binding n variables have only closed terms either side
data Tu :: Nat -> * where
  TH :: Tu Z
  TL :: Tu m -> Tu (S m)
  TK :: Tu m -> Tu m
  TF :: Tu m -> Cl -> Tu m
  TA :: Cl -> Tu m -> Tu m
deriving instance Show (Tu m)

-- abacus addition adds number bound to number free
type family Abacus (m :: Nat) (n :: Nat) :: Nat where
  Abacus Z n = n
  Abacus (S m) n = Abacus m (S n)

-- underground relevant terms are either closed,
-- or they're tubes which bring us to a station
data Un :: Nat -> * where
  UC :: Cl -> Un Z
  UTJ :: Natty m -> Tu m -> St (Abacus m (S n)) -> Un (S n)
deriving instance Show (Un n)

-- for every term, we can find the variables it actually uses and
-- build the underground relevant representation over just those,
-- with the OPE that embeds back where we came from
data TM :: Nat -> * where
  MkTM :: OPE n m -> Un n -> TM m
deriving instance Show (TM n)

tm :: Tm m -> TM m
tm (V i) = MkTM i (UTJ Zy TH It)
tm (L t) = case tm t of
  MkTM (OPE' r) (UC c)      -> MkTM r (UC (CK c))
  MkTM (OPE' r) (UTJ k t j) -> MkTM r (UTJ k (TK t) j)
  MkTM (OPES r) (UTJ k t j) -> case opeEnds r of
    (Zy, _)   -> MkTM r (UC (CL (UTJ k t j)))
    (Sy _, _) -> MkTM r (UTJ (Sy k) (TL t) j)
  MkTM (OPEI (Sy Zy))     (UTJ k t j) -> MkTM (OPEI Zy) (UC (CL (UTJ k t j)))
  MkTM (OPEI (Sy (Sy n))) (UTJ k t j) -> MkTM (OPEI (Sy n)) (UTJ (Sy k) (TL t) j)
tm (f :$ s) = case (tm f, tm s) of
  (MkTM r (UC cf), MkTM _ (UC cs))     -> MkTM r (UC (cf :$$ cs))
  (MkTM _ (UC cf), MkTM r (UTJ k t j)) -> MkTM r (UTJ k (TA cf t) j)
  (MkTM r (UTJ k t j), MkTM _ (UC cs)) -> MkTM r (UTJ k (TF t cs) j)
  (MkTM r uf@(UTJ _ _ _), MkTM r' us@(UTJ _ _ _)) -> case copOPE r r' of
    COPOPE p pr -> case ope2SSS p of
      OPE2SSS p -> MkTM pr (UTJ Zy TH (Ap p uf us))

-- we can still do a case analysis like it's a regular term, but
-- we get a reliable distinction between vacuous and relevant abstraction
caseUn :: Natty m ->
  p (S Z) ->
  (forall n n'. OPE2 n n' m -> Un n -> Un n' -> p m) ->
  (Un m -> p m) ->
  (Un (S m) -> p m) ->
  Un m -> p m
caseUn m v a k l (UC (f :$$ s))         = a (OPEII Zy) (UC f) (UC s)
caseUn m v a k l (UC (CK t))            = k (UC t)
caseUn m v a k l (UC (CL u))            = l u
caseUn m v a k l (UTJ Zy TH It)         = v
caseUn m v a k l (UTJ Zy TH (Ap p f s)) = a p f s
caseUn m v a k l (UTJ n (TK t) j)       = k (UTJ n t j)
caseUn m v a k l (UTJ (Sy n) (TL t) j)  = l (UTJ n t j)
caseUn m v a k l (UTJ n (TF t s) j)     = a (alll m) (UTJ n t j) (UC s)
caseUn m v a k l (UTJ n (TA f t) j)     = a (allr m) (UC f) (UTJ n t j)


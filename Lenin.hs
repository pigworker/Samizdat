{-----------------------------------------------------------------------------
An Effects-and-Handlers Implementation of Hindley-Milner Typechecking

Points of interest include

1. I use a free monad indexed over "Time" to represent computations which
   take time, during which progress can occur. Progress is packaged as the
   morphisms of the Time category, and is propagated rather quietly.
2. Instead of representing the typing context explicitly as a data structure,
   all contextualisation is done by effect handlers, responding to the effects
   enabled by the monad.

-----------------------------------------------------------------------------}


{-# LANGUAGE DataKinds, GADTs, KindSignatures, RankNTypes, StandaloneDeriving,
    QuantifiedConstraints, LambdaCase, ScopedTypeVariables, TypeOperators,
    TypeFamilies, UndecidableInstances, ConstraintKinds, TupleSections,
    IncoherentInstances, OverlappingInstances, PatternSynonyms,
    ViewPatterns, TypeOperators, LiberalTypeSynonyms, DeriveTraversable,
    ImpredicativeTypes #-}

module Lenin where

import Data.Kind      -- it's going to be this sort of adventure
import Unsafe.Coerce  -- and this sort

------------------------------------------------------------------------------
-- Indexing
------------------------------------------------------------------------------

-- index-respecting functions

type (-:>) s t i = s i -> t i
type (=:>) (c :: a -> Constraint)(t :: a -> Type)(i :: a) = c i => t i
type All f = forall i. f i
infixr 3 -:>
infixr 3 =:>


data (:*) (s :: a -> Type)(t :: a -> Type)(i :: a) where
  (:*) :: s i -> t i -> (s :* t) i
infixr 4 :*
fsti :: All ((s :* t) -:> s)
fsti (s :* _) = s
sndi :: All ((s :* t) -:> t)
sndi (_ :* t) = t

newtype K (t :: Type)(i :: a) = K {unK :: t} deriving Eq
type TyK (t :: Type)(i :: a) = t

type TyC (f :: b -> Type)(g :: a -> b)(i :: a) = f (g i)

kmap :: (s -> t) -> All (K s -:> K t)
kmap f (K s) = K (f s)

data Some (f :: a -> Type) :: Type where
  Some :: f x -> Some f
deriving instance (forall x. Show (f x)) => Show (Some f)


------------------------------------------------------------------------------
-- Time
------------------------------------------------------------------------------

data Time

-- Step sequences through time are snoc-lists which join up like dominoes
data (&>) (s :: Time)(t :: Time) :: Type where
  Now  :: t &> t
  (:<) :: r &> s -> Step s t -> r &> t

class Timed (v :: Time -> Type) where
  -- value-level &> gives the action of type-level &> ...
  (&>) :: v s -> s &> t -> v t
  -- ...by iterating the 
  step :: v s -> Step s t -> v t
  v &> Now = v
  v &> (sz :< s) = step (v &> sz) s

instance Timed ((&>) r) where
  step = (:<)

now :: v s -> s &> s
now _ = Now

instance Timed (K a) where
  K a &> _ = K a
  step (K a) _ = K a

instance (Timed s, Timed t) => Timed (s :* t) where
  step (s :* t) u = step s u :* step t u


class LE (s :: Time)(t :: Time) where
  lesson :: s &> t

class SegTo (t :: Time) where
  type SegFrom t :: Time
  seg :: SegFrom t &> t

instance LE s s where
  lesson = Now

instance (LE s (SegFrom t), SegTo t) => LE s t where
  lesson = lesson &> seg

type Kripke v t = forall u. LE t u => v u

kripke :: Timed v => All (v -:> Kripke v)
kripke v = v &> lesson

kripkefy :: Timed v => All (v -:> (Kripke v -:> f) -:> f)
kripkefy v k = k (kripke v)

type s !> t = (SegTo t, SegFrom t ~ s)

class MoTime (m :: (Time -> Type) -> (Time -> Type)) where
  retNow :: Timed v => All (v -:> m v)
  (>>>=) :: (Timed f, Timed g)
         => m f s
         -> All ((!>) s =:> Kripke f -:> m g)
         -> m g s
  (>>>)  :: (Timed f, Timed g)
         => m f s
         -> All ((!>) s =:> m g)
         -> m g s
  mf >>> mg = mf >>>= \ _ -> mg


split
  :: (Timed s, Timed t)
  => All ((s :* t) -:> (Kripke s -:> Kripke t -:> f) -:> f)
split (s :* t) f = f (kripke s) (kripke t)


------------------------------------------------------------------------------
-- de Bruijn Indices
------------------------------------------------------------------------------

-- natural numbers, for how many things are in scope
data N = Z | S N

-- de Bruijn indices, for which things are in scope
data Inx (n :: N) :: Type where
  Zi :: Inx (S n)
  Si :: Inx n -> Inx (S n)
deriving instance Eq (Inx n)
instance Show (Inx n) where
  show = show . go where
    go :: forall n. Inx n -> Int
    go Zi     = 0
    go (Si i) = 1  + go i

-------
-- if you know an Inx n, n isn't Z
data Pos (n :: N) :: Type where
  Pos :: Pos (S n)

inxPos :: Inx n -> Pos n
inxPos Zi = Pos
inxPos (Si _) = Pos
-------

-- thin j i is never j
thin :: Inx (S n) -> Inx n -> Inx (S n)
thin  Zi        i  = Si i
thin (Si j)  Zi    = Zi
thin (Si j) (Si i) = Si (thin j i)

-- thick j j = Nothing; thick j (thin j i) = i
thick :: Inx (S n) -> Inx (S n) -> Maybe (Inx n)
thick  Zi     Zi    = Nothing
thick  Zi    (Si j) = pure j
thick (Si j)  Zi    = case inxPos j of Pos -> pure Zi
thick (Si j) (Si i) = case inxPos j of Pos -> Si <$> thick i j


------------------------------------------------------------------------------
-- What changes with time?
------------------------------------------------------------------------------

data Step (s :: Time)(t :: Time) :: Type where
  (:/:) :: Ty Z -> ExVar -> Step t t

type ExVar =
  ( String  -- for mnemonic purposes
  , Int     -- for freshness
  )

data TyF t
  = t :-> t
  | t :*: t
  | Two
  deriving (Show, Eq, Functor, Foldable, Traversable)

data Ty (n :: N)
  = E ExVar            -- existential type variables
  | U (Inx n)          -- universal type variables
  | C (TyF (Ty n))     -- canonical type
  deriving (Show, Eq)

closed :: Ty Z -> Ty n
closed = unsafeCoerce

newtype Tyme (t :: Time) = Ty {unTy :: Ty Z} deriving (Show, Eq)

tiE :: All (K ExVar -:> Tyme)
tiE (K e) = Ty (E e)
tiC :: All (TyC TyF Tyme -:> Tyme)
tiC ft = Ty (C (fmap unTy ft))

data TyView (i :: Time) where
  SeeE :: K ExVar i -> TyView i
  SeeC :: TyF (Kripke Tyme i) -> TyView i

tyView :: All (Tyme -:> TyView)
tyView (Ty (E e))  = SeeE (K e)
tyView (Ty (C ft)) = SeeC (fmap (kripke . Ty) ft)

newtype CanTy (t :: Time) = CanTy (TyF (Tyme t))
instance Timed CanTy where
  step (CanTy ft) u = CanTy (fmap (`step` u) ft)

instance Timed Tyme where
  step (Ty t) (r :/: x) = Ty (subst r x t)

subst :: Ty Z -> ExVar -> Ty n -> Ty n
subst r x = go where
  go (E y) | x == y = closed r
  go (C ft) = C (fmap go ft)
  go t = t

data Sch (n :: N)
  = T (Ty n)
  | P (Sch (S n))
  deriving Show

newtype Schime (t :: Time) = Sch (Sch Z) deriving Show

monotype :: All (Tyme -:> Schime)
monotype (Ty t) = Sch (T t)

dep :: ExVar -> Ty n -> Bool
dep x (E y) = x == y
dep x (C ft) = any (dep x) ft
dep _ _ = False

instance Timed Schime where
  step (Sch s) (r :/: x) = Sch (go s) where
    go :: All (Sch -:> Sch)
    go (T t) = T (subst r x t)
    go (P s) = P (go s)
    
stan :: Sch (S Z) -> All (Tyme -:> Schime)
stan s (Ty r) = Sch (sub Zi s) where
  sub :: Inx (S n) -> Sch (S n) -> Sch n
  sub j (T t) = T (go t) where
    go (C ft) = C (fmap go ft)
    go (U i) = case thick j i of
      Nothing -> closed r
      Just i  -> U i
    go (E e) = E e
  sub j (P p) = P (sub (Si j) p)

gen :: All (K ExVar -:> Schime -:> Schime)
gen (K e) (Sch s) = case go Zi s of (s', b) -> if b then Sch (P s') else Sch s
 where

  go :: Inx (S n) -> Sch n -> (Sch (S n), Bool)
  go j (T t) = case euTy e j t of (t', b) -> (T t', b)
  go j (P s) = case go (Si j) s of (s', b) -> (P s', b)

  euTy :: ExVar -> Inx (S n) -> Ty n -> (Ty (S n), Bool)
  euTy e j (E x) = if e == x then (U j, True) else (E x, False)
  euTy _ j (U i) = (U (thin j i), False)
  euTy e j (C ft) = (C (fmap fst ft'), any snd ft') where
    ft' = fmap (euTy e j) ft

data Stux (t :: Time) =
  Stux {awaiting :: [ExVar], ready :: Bool}

instance Timed Stux where
  step (Stux ys b) (r :/: x)
    | elem x ys = case r of
        C _ -> Stux zs True
        E e -> Stux (e : zs) b
    | otherwise = Stux ys b
    where zs = [y | y <- ys, y /= x]

instance Semigroup (Stux t) where
  Stux ls a <> Stux rs b = Stux (ls ++ rs) (a || b)


------------------------------------------------------------------------------
-- Free Timed monads
------------------------------------------------------------------------------

data TiMo
  (c :: (Time -> Type) -> Time -> Type)
  (v :: Time -> Type)
  (s :: Time)
  :: Type where
  RetNow :: v s -> TiMo c v s
  Call :: forall c r v s
        . c r s
       -> All ((&>) s -:> r -:> TiMo c v)
       -> TiMo c v s

instance (forall r. Timed (c r), Timed v) => Timed (TiMo c v) where
  RetNow v &> u = RetNow (v &> u)
  Call c k &> u = Call (c &> u) $ \ w r -> k (u &> w) r
  step (RetNow v) u = RetNow (step v u)
  step (Call c k) u = Call (step c u) $ \ w r -> k ((Now :< u) &> w) r

instance MoTime (TiMo c) where
  retNow = RetNow
  (>>>=) :: forall c f g s. (Timed f, Timed g)
         => TiMo c f s
         -> All ((!>) s =:> Kripke f -:> TiMo c g)
         -> TiMo c g s
  RetNow v >>>= k = leap (now v) (k (kripke v))
  Call c j >>>= k = Call c $ \ u r ->
    j u r >>>= jump u seg
    where
      jump :: forall t t'. s &> t -> t &> t'
           -> Kripke f t' -> TiMo c g t'
      jump u w f = leap (u &> w) (k f)

op :: Timed r => c r s -> TiMo c r s
op c = Call c $ \ _ r -> RetNow r

leap :: forall s t x
      . s &> t
     -> (s !> t => x)
     -> x
leap u k = case mkStep u of
  Dict -> k


------------------------------------------------------------------------------
-- Seek not to know how the sausage is cooked
------------------------------------------------------------------------------

data Dict (c :: Constraint) :: Type where
  Dict :: c => Dict c

data FakeLe s t = FakeLe (s &> t)

mkStep :: forall s t. s &> t -> Dict (s !> t)
mkStep u = case (foo, baz) of
    (Dict, Dict) -> Dict
  where
  foo :: Dict (SegTo t)
  foo = unsafeCoerce (FakeLe u)
  bar :: Dict (s ~ s)
  bar = Dict
  baz :: Dict (SegFrom t ~ s)
  baz = unsafeCoerce bar


------------------------------------------------------------------------------
-- Effects
------------------------------------------------------------------------------

type ProgVar = String

data W (r :: Time -> Type)(i :: Time) :: Type where
  Next -- next fresh number, please (handled by nonce)
    :: W (K Int) i
  VSch -- look up the program variable (handled by decl)...
    :: ProgVar      -- ...with this name, and...
    -> W Schime i  -- tell me its type scheme
  Inst -- instantiate (handled by bloc)...
    :: Schime i  -- ...this type scheme...
    -> W Tyme i  -- ...to this type (by guessing the type parameters)
  Make -- make a definition (handled by guessing)...
    :: [ExVar]  -- ...with these dependencies to be extruded...
    -> Tyme i   -- ...of this type...
    -> ExVar    -- ...for this variable
    -> W (K ()) i
  Cano              -- wake me up when...
    :: Stux i       -- ...one of these variables is canonical
    -> W (K ()) i
  Barf :: W f i

instance Timed (W r) where
  step Next u = Next
  step (VSch x) u = VSch x
  step (Inst s) u = Inst (step s u)
  step (Make ds t x) u = Make ds (step t u) x
  step (Cano sx) u = Cano (step sx u)
  step Barf u = Barf


------------------------------------------------------------------------------
-- Handlers
------------------------------------------------------------------------------

-- handle Next...
nonce :: Timed v => Int -> All (TiMo W v -:> TiMo W v)
-- ...by giving the next number and rehandling the continuation with increment
nonce n (Call Next k) = nonce (n + 1) $ k Now (K n)
-- forward everything else
nonce n (RetNow v) = RetNow v
nonce n (Call c k) = Call c $ \ u r -> nonce n $ k u r

-- pick a fresh existential variable using Next
fresh :: String -> TiMo W (K ExVar) i
fresh x =
  op Next >>>= \ i ->
  retNow (kmap (x,) i)

-- handle VSch...
decl :: Timed v => ProgVar -> All (Schime -:> TiMo W v -:> TiMo W v)
-- ...by giving the scheme if we're looking up this decl
decl x s (Call (VSch y) k) | x == y = decl x s $ k Now s
-- forward everything else, but...
decl x s (RetNow v) = RetNow v
-- ...be sure to update the scheme in the light of progress
decl x s (Call c k) = Call c $ \ u r -> decl x (s &> u) $ k u r

-- handle Inst requests
--   (this is fatsemi in Gundry-McBride-McKinna
--   , doorstop in Krishnaswami-Dunfield)
bloc :: All (TiMo W Tyme -:> TiMo W Schime)
-- if we're instantiating a monotype, we're done
bloc (Call (Inst (Sch (T t))) k) = bloc $ k Now (Ty t)
-- if we're instantiating a polytime, we're inventing a fresh existential var
-- and guessing it
bloc (Call (Inst (Sch (P s))) k) =
  fresh "x" >>>= \ e ->
  guessing e $ bloc $
    op (Inst (stan s (tiE e))) >>>= \ t ->
    k lesson t
-- retNow wraps the type
bloc (RetNow (Ty t)) = RetNow (Sch (T t))
-- otherwise forward
bloc (Call c k) = Call c $ \ u r -> bloc $ k u r

-- handle Make, but also do generalisation (note we're computing type schemes)
guessing :: All (K ExVar -:> TiMo W Schime -:> TiMo W Schime)
-- when Make shows up, we have four possibilities
guessing (K e) (Call c@(Make ds (Ty t) x) k) = case (e == x, dep e t) of
  -- (is it me?, do I occur in the definiens)
  (True, True)  -- it's me and the occur check failed; oh noes!
    -> op Barf
  (True, False)  -- it's me, so extrude my dependencies and substitute me!
    -> foldr (guessing . K) (k (Now :< (t :/: x)) (K ())) ds
  (False, True)  -- it's not me, but I occur, so extrude me!
    -> Call (Make (e : ds) (Ty t) x) k
  (False, False)  -- it's nothing to do with me, so leave alone!
    -> Call c $ \ u r -> guessing (K e) $ k u r
-- nobody made me; I could be anything; pawn becomes queen!
guessing e (RetNow s) = RetNow (gen e s)
-- forward the rest (the update is a no-op)
guessing (K e) (Call c k) = Call c $ \ u r -> guessing (K e) $ k u r

(|||) :: (Timed f, Timed g) => All (TiMo W f -:> TiMo W g -:> TiMo W (f :* g))
Call (Cano (Stux _ True)) k ||| plang                       = k Now (K ()) ||| plang
planf                       ||| Call (Cano (Stux _ True)) k = planf        ||| k Now (K ())
RetNow f                    ||| plang                       = kripkefy f $ \ f -> plang >>>= \ g -> retNow (f :* g)
planf                       ||| RetNow g                    = kripkefy g $ \ g -> planf >>>= \ f -> retNow (f :* g)
planf@(Call (Cano fx) fk)   ||| plang@(Call (Cano gx) gk)       =
  Call (Cano (fx <> gx)) $ \ u r -> (planf &> u) ||| (plang &> u)
planf@(Call (Cano _) _)     ||| Call c k = Call c $ \ u r -> (planf &> u) ||| k u r
Call c k                    ||| plang = Call c $ \ u r -> k u r ||| (plang &> u)


------------------------------------------------------------------------------
-- Run
------------------------------------------------------------------------------

run :: TiMo W f i -> Either String (Some f)
run (RetNow r) = Right (Some r)
run (Call Barf _) = Left "Barf"
run (Call (Cano _) _) = Left "Blocking"


------------------------------------------------------------------------------
-- Core ML
------------------------------------------------------------------------------

data Tm
  = V ProgVar              -- program variables
  | ProgVar :=> Tm         -- lambda
  | Tm :$ Tm               -- application
  | (ProgVar, Tm) :/ Tm    -- let
  deriving Show

infixr 3 :/
infixr 4 :=>
infixl 5 :$


canTy :: All (Tyme -:> TiMo W CanTy)
canTy t = case tyView t of
  SeeC c -> retNow (CanTy (fmap (\ t -> t) c))
  SeeE (K e) -> kripkefy t $ \ t -> 
    op (Cano (Stux [e] False)) >>>
    canTy t

-- ensure that a type is a function type, giving back source and target
funTy :: All (Tyme -:> TiMo W (Tyme :* Tyme))
-- if it's already a function type, crack on!
funTy (Ty (C (s :-> t))) = retNow (Ty s :* Ty t)
-- otherwise, invent a function type and constrain
funTy u =
  op (Inst (Sch (P (P (T (C (U (Si Zi) :-> U Zi))))))) >>>= \ f ->
  unify (kripke u) f >>>= \ _ ->
  funTy f

-- guess a type
guess :: All (TiMo W Tyme)
guess = op (Inst (Sch (P (T (U Zi)))))

-- make types the same!
unify :: All (Tyme -:> Tyme -:> TiMo W (K ()))
-- if they're already the same, we're done
-- (note that catches trivial occur check failures, leaving only bad ones)
unify a b
  | a == b = retNow (K ())
  | otherwise = case (tyView a, tyView b) of
    (SeeE (K e), _) -> op (Make [] b e)
    (_, SeeE (K e)) -> op (Make [] a e)
    (SeeC (s0 :-> t0), SeeC (s1 :-> t1)) ->
      unify s0 s1 >>> unify t0 t1
    (SeeC (s0 :*: t0), SeeC (s1 :*: t1)) ->
      unify s0 s1 >>> unify t0 t1
    _ -> op Barf


infer :: Tm -> All (TiMo W Tyme)
infer (V x) =
  op (VSch x) >>>= \ s ->   -- look up the declaration
  op (Inst s)              -- instantiate it
infer (x :=> b) =
  guess >>>= \ s ->                           -- guess the domain
  decl x (monotype s) (infer b) >>>= \ t ->   -- declare x monomorphically
  retNow (tiC (s :-> t))                      -- assemble the function type
infer (f :$ a) =
  infer f >>>= \ ft ->    -- infer the function's type
  infer a >>>= \ at ->    -- infer the argument's type
  funTy ft >>>= \ st ->   -- see the function's type as a function type
    split st $ \ s t ->   -- split into domain and codomain
      unify at s >>>      -- unify argument's type with domain
      retNow t            -- give back the codomain
infer ((x, d) :/ b) =
  bloc (infer d) >>>= \ s ->  -- get a type scheme for the definiens
  decl x s (infer b)          -- declare the definiendum and infer the body


------------------------------------------------------------------------------
-- Entry point
------------------------------------------------------------------------------

whatIs :: Tm -> Either String (Sch Z)
whatIs t = case run . nonce 0 . bloc $ infer t of
  Right (Some (Sch s)) -> Right s
  Left e -> Left e

skk :: Either String (Sch Z)
skk = whatIs $
  ("s", "f" :=> "a" :=> "g" :=> V "f" :$ V "g" :$ (V "a" :$ V "g")) :/
  ("k", "x" :=> "g" :=> V "x") :/
  V "s" :$ V "k" :$ V "k"

myTest :: All (TiMo W Tyme)
myTest =
  guess >>>= \ s ->
  (foo s
   |||
   unify s (Ty (C Two))) >>>= \ st ->
     retNow (fsti st)
 where
  foo :: All (Tyme -:> TiMo W Tyme)
  foo s = kripkefy s $ \ s -> canTy s >>> retNow s
  
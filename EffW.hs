{-# LANGUAGE DataKinds, GADTs, KindSignatures, RankNTypes, StandaloneDeriving,
    QuantifiedConstraints, LambdaCase, ScopedTypeVariables, TypeOperators,
    TypeFamilies, UndecidableInstances, ConstraintKinds, TupleSections,
    IncoherentInstances, OverlappingInstances, PatternSynonyms,
    ViewPatterns, TypeOperators #-}

module EffW where

import Data.Kind      -- it's going to be this sort of adventure
import Unsafe.Coerce  -- and this sort


------------------------------------------------------------------------------
-- de Bruijn Indices
------------------------------------------------------------------------------

-- natural numbers, for how many things are in scope
data N = Z | S N

-- de Bruijn indices, for which things are in scope
data Inx (n :: N) :: Type where
  Zi :: Inx (S n)
  Si :: Inx n -> Inx (S n)
deriving instance Show (Inx n)
deriving instance Eq (Inx n)

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
-- Indexing
------------------------------------------------------------------------------

type (-:>) s t = forall i. s i -> t i   -- grumble want type lambda

data (:*) (s :: a -> Type)(t :: a -> Type)(i :: a) where
  (:*) :: s i -> t i -> (s :* t) i

data K (t :: Type)(i :: a) :: Type where
  K :: t -> K t i
  deriving Eq

unK :: K t i -> t
unK (K t) = t

kmap :: (s -> t) -> K s -:> K t
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

kripke :: Timed v => v t -> Kripke v t
kripke v = v &> lesson

kripkefy :: Timed v => v s -> (Kripke v s -> f s) -> f s
kripkefy v k = k (kripke v)


class MoTime (m :: (Time -> Type) -> (Time -> Type)) where
  retNow :: Timed v => v s -> m v s
  (>>>=)  :: (Timed f, Timed g)
         => m f s
         -> (forall t. (SegTo t, SegFrom t ~ s) =>
             Kripke f t -> m g t)
         -> m g s
  (>>>)  :: (Timed f, Timed g)
         => m f s
         -> (forall t. (SegTo t, SegFrom t ~ s) => m g t)
         -> m g s
  mf >>> mg = mf >>>= \ _ -> mg

split :: (Timed s, Timed t) => (s :* t) i -> (Kripke s i -> Kripke t i -> f i) -> f i
split (s :* t) f = f (kripke s) (kripke t)



------------------------------------------------------------------------------
-- What changes with time?
------------------------------------------------------------------------------

data Step (s :: Time)(t :: Time) :: Type where
  (:/:) :: Ty Z -> ExVar -> Step t t

type ExVar =
  ( String  -- for mnemonic purposes
  , Int     -- for freshness
  )

data Ty (n :: N)
  = E ExVar    -- existential type variables
  | U (Inx n)
  | Ty n :-> Ty n
  deriving (Show, Eq)

closed :: Ty Z -> Ty n
closed = unsafeCoerce

newtype Tyme (t :: Time) = Ty (Ty Z) deriving (Show, Eq)

tiE :: K ExVar t -> Tyme t
tiE (K e) = Ty (E e)

data UnArrEh (i :: Time) where
  UnArrAye :: Kripke Tyme i -> Kripke Tyme i -> UnArrEh i
  UnArrNaw :: UnArrEh i

unArrEh :: Tyme i -> UnArrEh i
unArrEh (Ty (s :-> t)) = kripkefy (Ty s) $ \ s -> kripkefy (Ty t) $ \ t ->
  UnArrAye s t
unArrEh _ = UnArrNaw

pattern (:-&>) :: Kripke Tyme i -> Kripke Tyme i -> Tyme i
pattern s :-&> t <- (unArrEh -> UnArrAye s t)

(-&>) :: Tyme t -> Tyme t -> Tyme t
Ty a -&> Ty b = Ty (a :-> b)

instance Timed Tyme where
  step (Ty t) (r :/: x) = Ty (subst r x t)

subst :: Ty Z -> ExVar -> Ty n -> Ty n
subst r x = go where
  go (E y) | x == y = closed r
  go (s :-> t) = go s :-> go t
  go t = t

data Sch (n :: N)
  = T (Ty n)
  | P (Sch (S n))
  deriving Show

newtype Schime (t :: Time) = Sch (Sch Z) deriving Show

monotype :: Tyme -:> Schime
monotype (Ty t) = Sch (T t)

dep :: ExVar -> Ty n -> Bool
dep x (E y) = x == y
dep x (s :-> t) = dep x s || dep x t
dep _ _ = False

instance Timed Schime where
  step (Sch s) (r :/: x) = Sch (go s) where
    go :: Sch -:> Sch
    go (T t) = T (subst r x t)
    go (P s) = P (go s)
    
stan :: Sch (S Z) -> Tyme -:> Schime
stan s (Ty r) = Sch (sub Zi s) where
  sub :: Inx (S n) -> Sch (S n) -> Sch n
  sub j (T t) = T (go t) where
    go (s :-> t) = go s :-> go t
    go (U i) = case thick j i of
      Nothing -> closed r
      Just i  -> U i
    go (E e) = E e
  sub j (P p) = P (sub (Si j) p)

gen :: ExVar -> Schime i -> Schime i
gen e (Sch s) = case go Zi s of (s', b) -> if b then Sch (P s') else Sch s
 where

  go :: Inx (S n) -> Sch n -> (Sch (S n), Bool)
  go j (T t) = case euTy e j t of (t', b) -> (T t', b)
  go j (P s) = case go (Si j) s of (s', b) -> (P s', b)

  euTy :: ExVar -> Inx (S n) -> Ty n -> (Ty (S n), Bool)
  euTy e j (E x) = if e == x then (U j, True) else (E x, False)
  euTy _ j (U i) = (U (thin j i), False)
  euTy e j (s :-> t) = case (euTy e j s, euTy e j t) of
    ((s, a), (t, b)) -> (s :-> t, a || b)


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
       -> (((&>) s :* r) -:> TiMo c v)
       -> TiMo c v s

instance (forall r. Timed (c r), Timed v) => Timed (TiMo c v) where
  RetNow v &> u = RetNow (v &> u)
  Call c k &> u = Call (c &> u) $ \ (w :* r) -> k ((u &> w) :* r)
  step (RetNow v) u = RetNow (step v u)
  step (Call c k) u = Call (step c u) $ \ (w :* r) -> k ((Now :< u) &> w :* r)

instance MoTime (TiMo c) where
  retNow = RetNow
  (>>>=) :: forall c f g s. (Timed f, Timed g)
         => TiMo c f s
         -> (forall t. (SegTo t, SegFrom t ~ s) =>
             Kripke f t -> TiMo c g t)
         -> TiMo c g s
  RetNow v >>>= k = leap (now v) (k (kripke v))
  Call c j >>>= k = Call c $ \ (u :* r) ->
    j (u :* r) >>>= jump u seg
    where
      jump :: forall t t'. s &> t -> t &> t'
           -> Kripke f t' -> TiMo c g t'
      jump u w f = leap (u &> w) (k f)

op :: Timed r => c r s -> TiMo c r s
op c = Call c $ \ (u :* r) -> RetNow r

leap :: forall s t x
      . s &> t
     -> ((SegTo t, SegFrom t ~ s) => x)
     -> x
leap u k = case mkStep u of
  Dict -> k

------------------------------------------------------------------------------
-- Seek not to know how the sausage is cooked
------------------------------------------------------------------------------

data Dict (c :: Constraint) :: Type where
  Dict :: c => Dict c

data FakeLe s t = FakeLe (s &> t)

mkStep :: forall s t. s &> t -> Dict (SegTo t, (SegFrom t ~ s))
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
  Barf :: W f i

instance Timed (W r) where
  step Next u = Next
  step (VSch x) u = VSch x
  step (Inst s) u = Inst (step s u)
  step (Make ds t x) u = Make ds (step t u) x
  step Barf u = Barf


------------------------------------------------------------------------------
-- Handlers
------------------------------------------------------------------------------

-- handle Next...
nonce :: Timed v => Int -> TiMo W v i -> TiMo W v i
-- ...by giving the next number and rehandling the continuation with increment
nonce n (Call Next k) = nonce (n + 1) (k (Now :* K n))
-- forward everything else
nonce n (RetNow v) = RetNow v
nonce n (Call c k) = Call c $ nonce n . k

-- pick a fresh existential variable using Next
fresh :: String -> TiMo W (K ExVar) i
fresh x =
  op Next >>>= \ i ->
  retNow (kmap (x,) i)


type ProgVar = String
-- handle VSch...
decl :: Timed v => ProgVar -> Schime i -> TiMo W v i -> TiMo W v i
-- ...by giving the scheme if we're looking up this decl
decl x s (Call (VSch y) k) | x == y = decl x s $ k (Now :* s)
-- forward everything else, but...
decl x s (RetNow v) = RetNow v
-- ...be sure to update the scheme in the light of progress
decl x s (Call c k) = Call c $ \ (u :* r) -> decl x (s &> u) $ k (u :* r)

-- handle Inst requests
--   (this is fatsemi in Gundry-McBride-McKinna
--   , doorstop in Krishnaswami-Dunfield)
bloc :: TiMo W Tyme i -> TiMo W Schime i
-- if we're instantiating a monotype, we're done
bloc (Call (Inst (Sch (T t))) k) = bloc $ k (Now :* Ty t)
-- if we're instantiating a polytime, we're inventing a fresh existential var
-- and guessing it
bloc (Call (Inst (Sch (P s))) k) =
  fresh "x" >>>= \ e -> 
  guessing e $ bloc $
    op (Inst (stan s (tiE e))) >>>= \ t ->
    k (lesson :* t)
-- retNow wraps the type
bloc (RetNow (Ty t)) = RetNow (Sch (T t))
-- otherwise forward
bloc (Call c k) = Call c $ \ ur -> bloc $ k ur

-- handle Make, but also do generalisation (note we're computing type schemes)
guessing :: K ExVar i -> TiMo W Schime i -> TiMo W Schime i
-- when Make shows up, we have four possibilities
guessing (K e) (Call c@(Make ds (Ty t) x) k) = case (e == x, dep e t) of
  -- (is it me?, do I occur in the definiens)
  (True, True)  -- it's me and the occur check failed; oh noes!
    -> op Barf
  (True, False)  -- it's me, so extrude my dependencies and substitute me!
    -> foldr (guessing . K) (k (Now :< (t :/: x) :* K ())) ds
  (False, True)  -- it's not me, but I occur, so extrude me!
    -> Call (Make (e : ds) (Ty t) x) k
  (False, False)  -- it's nothing to do with me, so leave alone!
    -> Call c $ \ ur -> guessing (K e) $ k ur
-- nobody made me; I could be anything; pawn becomes queen!
guessing e (RetNow s) = RetNow (gen (unK e) s)
-- forward the rest (the update is a no-op)
guessing e (Call c k) = Call c $ \ (u :* r) -> guessing (e &> u) $ k (u :* r)


------------------------------------------------------------------------------
-- Run
------------------------------------------------------------------------------

run :: TiMo W f i -> Maybe (Some f)
run (RetNow r) = Just (Some r)
run _ = Nothing


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

-- ensure that a type is a function type, giving back source and target
funTy :: Tyme i -> TiMo W (Tyme :* Tyme) i
-- if it's already a function type, crack on!
funTy (Ty (s :-> t)) = retNow (Ty s :* Ty t)
-- otherwise, invent a function type and constrain
funTy u =
  op (Inst (Sch (P (P (T (U (Si Zi) :-> U Zi)))))) >>>= \ f ->
  unify (kripke u) f >>>= \ _ ->
  funTy f

-- guess a type
guess :: TiMo W Tyme i
guess = op (Inst (Sch (P (T (U Zi)))))

-- make types the same!
unify :: Tyme i -> Tyme i -> TiMo W (K ()) i
-- if they're already the same, we're done
-- (note that catches trivial occur check failures, leaving only bad ones)
unify a b | a == b = retNow (K ())
-- rigid-rigid decomposition
unify (s0 :-&> t0) (s1 :-&> t1) = unify s0 s1 >>> unify t0 t1
-- flex problem? demand a definition!
unify (Ty (E e)) t = op (Make [] t e)
unify t (Ty (E e)) = op (Make [] t e)
-- anything else is hopeless
unify _ _ = op Barf

infer :: Tm -> TiMo W Tyme i
infer (V x) =
  op (VSch x) >>>= \ s ->   -- look up the declaration
  op (Inst s)              -- instantiate it
infer (x :=> b) =
  guess >>>= \ s ->                           -- guess the domain
  decl x (monotype s) (infer b) >>>= \ t ->   -- declare x monomorphically
  retNow (s -&> t)                            -- assemble the function type
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

whatIs :: Tm -> Maybe (Sch Z)
whatIs t = case run . nonce 0 . bloc $ infer t of
  Just (Some (Sch s)) -> Just s
  _ -> Nothing

skk :: Maybe (Sch Z)
skk = whatIs $
  ("s", "f" :=> "a" :=> "g" :=> V "f" :$ V "g" :$ (V "a" :$ V "g")) :/
  ("k", "x" :=> "g" :=> V "x") :/
  V "s" :$ V "k" :$ V "k"

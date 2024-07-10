{-# LANGUAGE DataKinds, GADTs, KindSignatures, RankNTypes, StandaloneDeriving,
    QuantifiedConstraints, LambdaCase, ScopedTypeVariables, TypeOperators,
    TypeFamilies, UndecidableInstances, ConstraintKinds, TupleSections,
    IncoherentInstances, OverlappingInstances, PatternSynonyms,
    ViewPatterns, TypeOperators #-}

module EffW where

import Data.Kind
import Data.List
import Unsafe.Coerce

------------------------------------------------------------------------------
-- Dict
------------------------------------------------------------------------------

data Dict (c :: Constraint) :: Type where
  Dict :: c => Dict c
  

------------------------------------------------------------------------------
-- Indexing
------------------------------------------------------------------------------

data (:*) (s :: a -> Type)(t :: a -> Type)(i :: a) where
  (:*) :: s i -> t i -> (s :* t) i

data K (t :: Type)(i :: a) :: Type where
  K :: t -> K t i
  deriving Eq

unK :: K t i -> t
unK (K t) = t

kmap :: (s -> t) -> K s i -> K t i
kmap f (K s) = K (f s)

data Some (f :: a -> Type) :: Type where
  Some :: f x -> Some f
deriving instance (forall x. Show (f x)) => Show (Some f)

------------------------------------------------------------------------------
-- Time
------------------------------------------------------------------------------

data Time

class Timed (v :: Time -> Type) where
  (&>) :: v s -> s &> t -> v t
  tick :: v s -> Step s t -> v t
  v &> Now = v
  v &> (sz :< s) = tick (v &> sz) s

data (&>) (s :: Time)(t :: Time) :: Type where
  Now  :: t &> t
  (:<) :: r &> s -> Step s t -> r &> t

instance Timed ((&>) r) where
  tick = (:<)

now :: v s -> s &> s
now _ = Now

instance Timed (K a) where
  K a &> _ = K a
  tick (K a) _ = K a

instance (Timed s, Timed t) => Timed (s :* t) where
  tick (s :* t) u = tick s u :* tick t u




class LE (s :: Time)(t :: Time) where
  lesson :: s &> t

class StepTo (t :: Time) where
  type StepFrom t :: Time
  step :: StepFrom t &> t

instance LE s s where
  lesson = Now

instance (LE s (StepFrom t), StepTo t) => LE s t where
  lesson = lesson &> step

type Kripke v t = forall u. LE t u => v u

kripke :: Timed v => v s -> Kripke v s
kripke v = v &> lesson

kripkefy :: Timed v => v s -> (Kripke v s -> f s) -> f s
kripkefy v k = k (kripke v)


class MoTime (m :: (Time -> Type) -> (Time -> Type)) where
  retNow :: Timed v => v s -> m v s
  (>>>=) :: (Timed f, Timed g)
         => m f s
         -> (forall t. (StepTo t, StepFrom t ~ s) =>
             Kripke f t -> m g t)
         -> m g s

split :: (Timed s, Timed t) => (s :* t) i -> (Kripke s i -> Kripke t i -> f i) -> f i
split (s :* t) f = f (kripke s) (kripke t)



------------------------------------------------------------------------------
-- What changes with time?
------------------------------------------------------------------------------

data Step (s :: Time)(t :: Time) :: Type where
  (:/:) :: Ty -> (String, Int) -> Step t t

data Ty
  = E (String, Int)
  | U Int
  | Ty :-> Ty
  deriving (Show, Eq)

newtype Tyme (t :: Time) = Ty Ty deriving (Show, Eq)

tiE :: K (String, Int) t -> Tyme t
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
  tick (Ty t) (r :/: x) = Ty (go t) where
    go (E y) | x == y = r
    go (s :-> t) = go s :-> go t
    go t = t

data Sch
  = T Ty
  | P Sch
  deriving Show

newtype Schime (t :: Time) = Sch Sch deriving Show

tiT :: Tyme t -> Schime t
tiT (Ty t) = Sch (T t)

dep :: (String, Int) -> Ty -> Bool
dep x (E y) = x == y
dep x (s :-> t) = dep x s || dep x t
dep _ _ = False

instance Timed Schime where
  tick (Sch (T t)) u = Sch (T t') where Ty t' = tick (Ty t) u
  tick (Sch (P s)) u = Sch (P s') where Sch s' = tick (Sch s) u

stan :: Schime t -> Tyme t -> Schime t
stan (Sch s) (Ty t) = Sch (sub 0 t s) where
  sub :: Int -> Ty -> Sch -> Sch
  sub n u (T t) = T (go t) where
    go (s :-> t) = go s :-> go t
    go (U k) | k == n = u
    go t = t
  sub n u (P p) = P (sub (n + 1) u p)

gen :: (String, Int) -> Schime i -> Schime i
gen e (Sch s) = case go 0 s of (s, b) -> if b then Sch (P s) else Sch s
 where

  go :: Int -> Sch -> (Sch, Bool)
  go u (T t) = case euTy e u t of (t, b) -> (T t, b)
  go u (P s) = case go (u + 1) s of (s, b) -> (P s, b)

  euTy :: (String, Int) -> Int -> Ty -> (Ty, Bool)
  euTy e u (E x) = if e == x then (U u, True) else (E x, False)
  euTy _ _ (U u) = (U u, False)
  euTy e u (s :-> t) = case (euTy e u s, euTy e u t) of
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
       -> (forall t. s &> t -> r t -> TiMo c v t)
       -> TiMo c v s

instance (forall r. Timed (c r), Timed v) => Timed (TiMo c v) where
  RetNow v &> u = RetNow (v &> u)
  Call c k &> u = Call (c &> u) $ \ w -> k (u &> w)
  tick (RetNow v) u = RetNow (tick v u)
  tick (Call c k) u = Call (tick c u) $ \ w -> k ((Now :< u) &> w)

instance MoTime (TiMo c) where
  retNow = RetNow
  (>>>=) :: forall c f g s. (Timed f, Timed g)
         => TiMo c f s
         -> (forall t. (StepTo t, StepFrom t ~ s) =>
             Kripke f t -> TiMo c g t)
         -> TiMo c g s
  RetNow v >>>= k = leap (now v) (k (kripke v))
  Call c j >>>= k = Call c $ \ u r ->
    j u r >>>= jump u step
    where
      jump :: forall t t'. s &> t -> t &> t'
           -> Kripke f t' -> TiMo c g t'
      jump u w f = leap (u &> w) (k f)

op :: Timed r => c r s -> TiMo c r s
op c = Call c $ \ u r -> RetNow r

leap :: forall s t x
      . s &> t
     -> ((StepTo t, StepFrom t ~ s) => x)
     -> x
leap u k = case mkStep u of
  Dict -> k


------------------------------------------------------------------------------
-- Seek not to know how the sausage is cooked
------------------------------------------------------------------------------

data FakeLe s t = FakeLe (s &> t)

mkStep :: forall s t. s &> t -> Dict (StepTo t, (StepFrom t ~ s))
mkStep u = case (foo, baz) of
    (Dict, Dict) -> Dict
  where
  foo :: Dict (StepTo t)
  foo = unsafeCoerce (FakeLe u)
  bar :: Dict (s ~ s)
  bar = Dict
  baz :: Dict (StepFrom t ~ s)
  baz = unsafeCoerce bar


------------------------------------------------------------------------------
-- Effects
------------------------------------------------------------------------------

data W (r :: Time -> Type)(i :: Time) :: Type where
  Next -- next fresh number, please (handled by nonce)
    :: W (K Int) i
  VSch -- look up the program variable (handled by decl)...
    :: String      -- ...with this name, and...
    -> W Schime i  -- tell me its type scheme
  Inst -- instantiate (handled by bloc)...
    :: Schime i  -- ...this type scheme...
    -> W Tyme i  -- ...to this type (by guessing the type parameters)
  Make -- make a definition (handled by guessing)...
    :: [(String, Int)]  -- ...with these dependencies to be extruded...
    -> Tyme i           -- ...of this type...
    -> (String, Int)    -- ...for this variable
    -> W (K ()) i
  Barf :: W f i

instance Timed (W r) where
  tick Next u = Next
  tick (VSch x) u = VSch x
  tick (Inst s) u = Inst (tick s u)
  tick (Make ds t x) u = Make ds (tick t u) x
  tick Barf u = Barf


------------------------------------------------------------------------------
-- Handlers
------------------------------------------------------------------------------

-- handle Next...
nonce :: Timed v => Int -> TiMo W v i -> TiMo W v i
-- ...by giving the next number and rehandling the continuation with increment
nonce n (Call Next k) = nonce (n + 1) (k Now (K n))
-- forward everything else
nonce n (RetNow v) = RetNow v
nonce n (Call c k) = Call c $ \ u r -> nonce n (k u r)

-- handle VSch...
decl :: Timed v => String -> Schime i -> TiMo W v i -> TiMo W v i
-- ...by giving the scheme if we're looking up this decl
decl x s (Call (VSch y) k) | x == y = decl x s (k Now s)
-- forward everything else, but...
decl x s (RetNow v) = retNow v
-- ...be sure to update the scheme in the light of progress
decl x s (Call c k) = Call c $ \ u r -> decl x (s &> u) (k u r)

-- handle Inst requests
--   (this is fatsemi in Gundry-McBride-McKinna
--   , doorstop in Krishnaswami-Dunfield)
bloc :: TiMo W Tyme i -> TiMo W Schime i
-- if we're instantiating a monotype, we're done
bloc (Call (Inst (Sch (T t))) k) = bloc $ k Now (Ty t)
-- if we're instantiating a polytime, we're inventing a fresh existential var
-- and guessing it
bloc (Call (Inst (Sch (P s))) k) =
  fresh "x" >>>= \ e -> 
  guessing e . bloc $ (
    op (Inst (stan (Sch s) (tiE e))) >>>= \ t ->
    k lesson t
    )
-- return wraps the type
bloc (RetNow (Ty t)) = RetNow (Sch (T t))
-- otherwise forward
bloc (Call c k) = Call c $ \ u r -> bloc (k u r)

-- handle Make, but also do generalisation (note we're computing type schemes)
guessing :: K (String, Int) i -> TiMo W Schime i -> TiMo W Schime i
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
    -> Call c $ \ u r -> guessing (K e) (k u r)
-- nobody made me; I could be anything; pawn becomes queen!
guessing e (RetNow s) = RetNow (gen (unK e) s)
-- forward the rest (the update is a no-op)
guessing e (Call c k) = Call c $ \ u r -> guessing (e &> u) (k u r)



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
  = V String
  | String :=> Tm
  | Tm :$ Tm
  | (String, Tm) :/ Tm
  deriving Show

infixr 3 :/
infixr 4 :=>
infixl 5 :$

-- pick a fresh existential variable using Next
fresh :: String -> TiMo W (K (String, Int)) i
fresh x =
  op Next >>>= \ i ->
  retNow (kmap (x,) i)

-- ensure that a type is a function type, giving back source and target
funTy :: Tyme i -> TiMo W (Tyme :* Tyme) i
-- if it's already a function type, crack on!
funTy (Ty (s :-> t)) = retNow (Ty s :* Ty t)
-- otherwise, invent a function type and constrain
funTy u =
  op (Inst (Sch (P (P (T (U 1 :-> U 0)))))) >>>= \ f ->
  unify (kripke u) f >>>= \ _ ->
  funTy f

-- guess a type
guess :: TiMo W Tyme i
guess = op (Inst (Sch (P (T (U 0)))))

-- make types the same!
unify :: Tyme i -> Tyme i -> TiMo W (K ()) i
-- if they're already the same, we're done
-- (note that catches trivial occur check failures, leaving only bad ones)
unify a b | a == b = retNow (K ())
-- rigid-rigid decomposition
unify (s0 :-&> t0) (s1 :-&> t1) =
  -- solve the subproblems
  unify s0 s1 >>>= \ _ ->
  unify t0 t1
-- flex problem? demand a definition!
unify (Ty (E e)) t = op (Make [] t e)
unify t (Ty (E e)) = op (Make [] t e)
-- anything else is hopeless
unify _ _ = op Barf

infer :: Tm -> TiMo W Tyme i
infer (V x) =
  op (VSch x) >>>= \ s ->  -- look up the declaration
  op (Inst s)              -- instantiate it
infer (x :=> b) =
  guess >>>= \ s ->                      -- guess the domain
  decl x (tiT s) (infer b) >>>= \ t ->   -- declare x monomorphically
  retNow (s -&> t)                       -- assemble the function type
infer (f :$ a) =
  infer f >>>= \ ft ->        -- infer the function's type
  infer a >>>= \ at ->        -- infer the argument's type
  funTy ft >>>= \ st ->       -- see the function's type as a function type
    split st $ \ s t ->       -- split into domain and codomain
      unify at s >>>= \ _ ->  -- unify argument's type with domain
      retNow t                -- give back the codomain
infer ((x, d) :/ b) =
  bloc (infer d) >>>= \ s ->  -- get a type scheme for the definiens
  decl x s (infer b)          -- declare the definiendum and infer the body


------------------------------------------------------------------------------
-- Entry point
------------------------------------------------------------------------------

what's :: Tm -> Maybe Sch
what's t = case run . nonce 0 . bloc $ infer t of
  Just (Some (Sch s)) -> Just s
  _ -> Nothing

skk :: Maybe Sch
skk =  what's $
  ("s", "f" :=> "a" :=> "g" :=> V "f" :$ V "g" :$ (V "a" :$ V "g")) :/
  ("k", "x" :=> "g" :=> V "x") :/
  V "s" :$ V "k" :$ V "k"
{-# LANGUAGE DataKinds, GADTs, KindSignatures, RankNTypes, StandaloneDeriving,
    QuantifiedConstraints, LambdaCase, ScopedTypeVariables, TypeOperators,
    TypeFamilies, UndecidableInstances, ConstraintKinds, TupleSections,
    IncoherentInstances, OverlappingInstances,
    TypeOperators #-}

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

data Time = Tick Time

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
  (:/:) :: Ty -> (String, Int) -> Step t (Tick t)

data Ty
  = E (String, Int)
  | U Int
  | Ty :-> Ty
  deriving (Show, Eq)

newtype Tyme (t :: Time) = Ty Ty deriving (Show, Eq)

tiE :: K (String, Int) t -> Tyme t
tiE (K e) = Ty (E e)

tiArr :: Tyme t -> Tyme t -> Tyme t
tiArr (Ty a) (Ty b) = Ty (a :-> b)

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
  Next :: W (K Int) i
  VSch :: String -> W Schime i
  Inst :: Schime i -> W Tyme i
  Make :: [(String, Int)] -> Tyme i -> (String, Int) -> W (K ()) i
  Defn :: Tyme i -> (String, Int) -> W (K ()) i
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

decl :: Timed v => String -> Schime i -> TiMo W v i -> TiMo W v i
decl x s (Call (VSch y) k) | x == y = decl x s (k Now s)
decl x s (RetNow v) = retNow v
decl x s (Call c k) = Call c $ \ u r -> decl x (s &> u) (k u r)

nonce :: Timed v => Int -> TiMo W v i -> TiMo W v i
nonce n (Call Next k) = nonce (n + 1) (k Now (K n))
nonce n (RetNow v) = RetNow v
nonce n (Call c k) = Call c $ \ u r -> nonce n (k u r)

guessing :: K (String, Int) i -> TiMo W Schime i -> TiMo W Schime i
guessing e (RetNow s) = RetNow (gen (unK e) s)
guessing (K e) (Call c@(Make ds (Ty t) x) k) = case (e == x, dep e t) of
  (True, True)  -> op Barf
  (True, False) ->
    op (Defn (Ty t) x) >>>= \ v ->
    foldr (guessing . K) (k lesson v) ds
  (False, True) -> Call (Make (e : ds) (Ty t) x) k
  (False, False) -> Call c $ \ u r -> guessing (K e) (k u r)
guessing e (Call c k) = Call c $ \ u r -> guessing (e &> u) (k u r)

bloc :: TiMo W Tyme i -> TiMo W Schime i
bloc (Call (Inst (Sch (T t))) k) = bloc $ k Now (Ty t)
bloc (Call (Inst (Sch (P s))) k) =
  fresh "x" >>>= \ e -> 
  guessing e . bloc $ (
    op (Inst (stan (Sch s) (tiE e))) >>>= \ t ->
    k lesson t
    )
bloc (RetNow (Ty t)) = RetNow (Sch (T t))
bloc (Call c k) = Call c $ \ u r -> bloc (k u r)



------------------------------------------------------------------------------
-- Run
------------------------------------------------------------------------------

run :: TiMo W f i -> Maybe (Some f)
run (RetNow r) = Just (Some r)
run (Call (Defn (Ty t) x) k) = run (k (Now :< (t :/: x)) (K ()))
run _ = Nothing


------------------------------------------------------------------------------
-- Core ML
------------------------------------------------------------------------------

data Tm
  = V String
  | L String Tm
  | A Tm Tm
  | D (String, Tm) Tm
  deriving Show

fresh :: String -> TiMo W (K (String, Int)) i
fresh x = op Next >>>= \ i -> retNow (kmap (x,) i)

funTy :: Tyme i -> TiMo W (Tyme :* Tyme) i
funTy (Ty (s :-> t)) = retNow (Ty s :* Ty t)
funTy u =
  op (Inst (Sch (P (P (T (U 1 :-> U 0)))))) >>>= \ f ->
  unify (kripke u) f >>>= \ _ ->
  funTy f

guess :: TiMo W Tyme i
guess = op (Inst (Sch (P (T (U 0)))))

unify :: Tyme i -> Tyme i -> TiMo W (K ()) i
unify a b | a == b = retNow (K ())
unify (Ty (s0 :-> t0)) (Ty (s1 :-> t1)) =
  kripkefy (Ty s0) $ \ s0 -> kripkefy (Ty t0) $ \ t0 ->
  kripkefy (Ty s1) $ \ s1 -> kripkefy (Ty t1) $ \ t1 ->
  unify s0 s1 >>>= \ _ ->
  unify t0 t1
unify (Ty (E e)) t = op (Make [] t e)
unify t (Ty (E e)) = op (Make [] t e)
unify _ _ = op Barf

infer :: Tm -> TiMo W Tyme i
infer (V x) = op (VSch x) >>>= \ s -> op (Inst s)
infer (L x b) =
  guess >>>= \ s ->
  decl x (tiT s) (infer b) >>>= \ t ->
  retNow (tiArr s t)
infer (A f a) =
  infer f >>>= \ ft ->
  infer a >>>= \ at ->
  funTy ft >>>= \ st -> (split st $ \ s t ->
    unify at s >>>= \ _ ->
    retNow t)
infer (D (x, d) b) =
  bloc (infer d) >>>= \ s ->
  decl x s (infer b)

{-# LANGUAGE DataKinds, GADTs, KindSignatures, RankNTypes, StandaloneDeriving,
    QuantifiedConstraints, LambdaCase, ScopedTypeVariables,
    TypeFamilies, UndecidableInstances, ConstraintKinds,
    IncoherentInstances, OverlappingInstances, TypeOperators #-}

module Main where

import Data.Constraint
import Unsafe.Coerce

data Time = Z | S Time deriving Show
data Timey (t :: Time) :: * where
  Zy :: Timey Z
  Sy :: Timey n -> Timey (S n)

data Le :: Time -> Time -> * where
  Now    :: Le t t
  Later  :: Le s t -> Le s (S t)
deriving instance Show (Le s t)

class Timed (v :: Time -> *) where
  (&>) :: v s -> Le s t -> v t

instance Timed (Le s) where
  v &> Now = v
  v &> Later u = Later (v &> u)

class LE (s :: Time)(t :: Time) where
  lesson :: Le s t

instance LE s s where
  lesson = Now

class StepTo (t :: Time) where
  type StepFrom t :: Time
  step :: Le (StepFrom t) t

instance (LE s (StepFrom t), StepTo t) => LE s t where
  lesson = lesson &> step

data FakeLe s t = FakeLe (Le s t)

mkStep :: forall s t. Le s t -> Dict (StepTo t, (StepFrom t ~ s))
mkStep u = case (foo, baz) of
    (Dict, Dict) -> Dict
  where
  foo :: Dict (StepTo t)
  foo = unsafeCoerce (FakeLe u)
  bar :: Dict (s ~ s)
  bar = Dict
  baz :: Dict (StepFrom t ~ s)
  baz = unsafeCoerce bar

leap :: forall s t x
      . Le s t
     -> ((StepTo t, StepFrom t ~ s) => x)
     -> x
leap u k = case mkStep u of
  Dict -> k

type Kripke v t = forall u. LE t u => v u

kripke :: Timed v => v s -> Kripke v s
kripke v = v &> lesson

class MoTime (m :: (Time -> *) -> (Time -> *)) where
  retNow :: Timed v => v s -> m v s
  (>>>=) :: (Timed f, Timed g)
         => m f s
         -> (forall t. (StepTo t, StepFrom t ~ s) =>
             Kripke f t -> m g t)
         -> m g s

data TiMo
  (c :: (Time -> *) -> Time -> *)
  (v :: Time -> *)
  (s :: Time)
  :: * where
  RetNow :: v s -> TiMo c v s
  Call :: forall c r v s
        . c r s
       -> (forall t. Le s t -> r t -> TiMo c v t)
       -> TiMo c v s

instance (forall r. Timed (c r), Timed v) => Timed (TiMo c v) where
  RetNow v &> u = RetNow (v &> u)
  Call c k &> u = Call (c &> u) $ \ w -> k (u &> w)

now :: v s -> Le s s
now _ = Now

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
      jump :: forall t t'. Le s t -> Le t t'
           -> Kripke f t' -> TiMo c g t'
      jump u w f = leap (u &> w) (k f)

op :: Timed r => c r s -> TiMo c r s
op c = Call c $ \ u r -> RetNow r

newtype Ticky (t :: Time) = Clock Int deriving Show

instance Timed Ticky where
  x &> Now = x
  x &> Later u = case x &> u of
    Clock i -> Clock (i + 1)

data Cmd (r :: Time -> *)(s :: Time) :: * where
  Grab :: Cmd Ticky s
  Emit :: Ticky s -> Cmd (K ()) s
  Wait :: Cmd (K ()) s

instance Timed (Cmd b) where
  Grab   &> u = Grab
  Emit x &> u = Emit (x &> u)
  Wait   &> u = Wait

data K (a :: *)(s :: Time) :: * where
  K :: a -> K a s
instance Show a => Show (K a s) where show (K a) = show a
instance Timed (K a) where
  K a &> _ = K a

run :: forall s v. (forall i. Show (v i)) => Timey s -> TiMo Cmd v s -> IO ()
run _ (RetNow v) = print v
run s (Call Wait k) = wait Now s where
  wait :: forall t. Le s t -> Timey t -> IO ()
  wait u t = do
    putStrLn "waiting"
    getLine >>= \case
      "" -> wait (Later u) (Sy t)
      _  -> run t (k u (K ()))
run s (Call Grab k) = run s (k Now (Clock 0))
run s (Call (Emit (Clock x)) k) = do
  print x
  run s (k Now (K ()))

myProg :: TiMo Cmd (K ()) Z
myProg =
  op Grab >>>= \ x ->
  op Wait >>>= \ _ ->
  op (Emit x) >>>= \ _ ->
  retNow (K ())

myProg' :: TiMo Cmd (K ()) Z
myProg' =
  op Grab >>>= \ x ->
  op Wait >>>= \ _ ->
  op Grab >>>= \ y ->
  op (Emit x) >>>= \ _ ->
  -- retNow x >>>= \ x ->
  op (Emit y) >>>= \ _ ->
  op Wait >>>= \ _ ->
  op (Emit x) >>>= \ _ ->
  op (Emit y) >>>= \ _ ->
  retNow (K ())

main :: IO ()
main = run Zy myProg
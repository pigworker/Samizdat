{-# LANGUAGE DataKinds, GADTs, KindSignatures, StandaloneDeriving, RankNTypes #-}

module BigArray where

import Data.Monoid
import Control.Applicative
import Data.Functor.Identity

data Nat = Ze | Su Nat

data Bnd k = Bot | Key k | Top deriving (Ord, Eq, Show)

data T23 (n :: Nat) (k :: *) (v :: *) where
  Leaf   :: T23 Ze k v
  Node2  :: T23 n k v -> (k, v) -> T23 n k v -> T23 (Su n) k v
  Node3  :: T23 n k v -> (k, v) -> T23 n k v -> (k, v) -> T23 n k v -> T23 (Su n) k v
deriving instance (Show k, Show v) => Show (T23 n k v)

data I23 n k v where
  Level :: T23 n k v -> I23 n k v
  Grow2 :: T23 n k v -> (k, v) -> T23 n k v -> I23 n k v

find23 :: Ord k => k -> T23 n k v -> Maybe v
find23 k Leaf = Nothing
find23 k (Node2 lj (j, jv) ju) = case compare k j of
  LT -> find23 k lj
  EQ -> Just jv
  GT -> find23 k ju
find23 k (Node3 li (i, iv) ij (j, jv) ju) = case (compare k i, compare k j) of
  (LT, _) -> find23 k li
  (EQ, _) -> Just iv
  (_, LT) -> find23 k ij
  (_, EQ) -> Just jv
  (_, GT) -> find23 k ju

insert23 :: Ord k => (k, v) -> T23 n k v -> I23 n k v
insert23 iv Leaf = Grow2 Leaf iv Leaf
insert23 iv@(i, _) (Node2 lj jv@(j, _) ju) =
  case compare i j of
    LT -> case insert23 iv lj of
      Grow2 lh hv hj -> Level (Node3 lh hv hj jv ju)
      Level lj       -> Level (Node2 lj jv ju)
    EQ -> Level (Node2 lj iv ju)
    GT -> case insert23 iv ju of
      Grow2 jk kv ku -> Level (Node3 lj jv jk kv ku)
      Level ju       -> Level (Node2 lj jv ju)
insert23 iv@(i, _) (Node3 lj jv@(j, _) jk kv@(k, _) ku) =
  case (compare i j, compare i k) of
    (LT, _) -> case insert23 iv lj of
      Grow2 lh hv hj -> Grow2 (Node2 lh hv hj) jv (Node2 jk kv ku)
      Level lj       -> Level (Node3 lj jv jk kv ku)
    (EQ, _) -> Level (Node3 lj iv jk kv ku)
    (_, LT) -> case insert23 iv jk of
      Grow2 jh hv hk -> Grow2 (Node2 lj jv jh) hv (Node2 hk kv ku)
      Level jk       -> Level (Node3 lj jv jk kv ku)
    (_, EQ) -> Level (Node3 lj jv jk iv ku)
    (_, GT) -> case insert23 iv ku of
      Grow2 kh hv hu -> Grow2 (Node2 lj jv jk) kv (Node2 kh hv hu)
      Level ku       -> Level (Node3 lj jv jk kv ku)

data Arr (k :: *)(v :: *) where
  Arr :: T23 n k v -> Arr k v
deriving instance (Show k, Show v) => Show (Arr k v)

emptyArr :: Arr k v
emptyArr = Arr Leaf

insertArr :: Ord k => (k, v) -> Arr k v -> Arr k v
insertArr iv (Arr lu) = case insert23 iv lu of
  Level lu       -> Arr lu
  Grow2 lj jv ju -> Arr (Node2 lj jv ju)

findArr :: Ord k => k -> Arr k v -> Maybe v
findArr k (Arr lu) = find23 k lu

single :: Ord k => (k, v) -> Arr k v
single x = insertArr x emptyArr

isEmptyArr :: Arr k v -> Bool
isEmptyArr (Arr Leaf) = True
isEmptyArr _ = False

travT23 :: Applicative f => ((k, v) -> f w) -> T23 n k v -> f (T23 n k w)
travT23 f Leaf = pure Leaf
travT23 f (Node2 l x@(k, _) r) = Node2 <$> travT23 f l <*> ((,) k <$> f x) <*> travT23 f r
travT23 f (Node3 l x@(j, _) m y@(k, _) r) =
  Node3 <$> travT23 f l <*> ((,) j <$> f x) <*> travT23 f m <*> ((,) k <$> f y) <*> travT23 f r

travArr :: Applicative f => ((k, v) -> f w) -> Arr k v -> f (Arr k w)
travArr f (Arr t) = Arr <$> travT23 f t

foldMapArr :: Monoid x => ((k, v) -> x) -> Arr k v -> x
foldMapArr f = getConst . travArr (Const . f)

instance (Ord k, Monoid v) => Monoid (Arr k v) where  -- SEMIGROUP v!
  mempty = emptyArr
  mappend l r = appEndo (foldMapArr up l) r where
    up (k, v) = Endo $ \ r -> case findArr k r of
      Just w  -> insertArr (k, mappend v w) r
      Nothing -> insertArr (k, v) r

type Set x = Arr x ()

domain :: Ord k => Arr k v -> Set k
domain = runIdentity . travArr (\ (k, _) -> Identity ())

inSet :: Ord x => x -> Set x -> Bool
inSet x s = case findArr x s of
  Just _ -> True
  _      -> False

singleton :: Ord x => x -> Set x
singleton = single . flip (,) ()

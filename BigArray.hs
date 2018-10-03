{-# LANGUAGE DataKinds, GADTs, KindSignatures, StandaloneDeriving, RankNTypes,
    TypeSynonymInstances #-}

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

instance Functor (T23 n k) where
  fmap f Leaf = Leaf
  fmap f (Node2 l (k, v) r) = Node2 (fmap f l) (k, f v) (fmap f r)
  fmap f (Node3 l (j, u) m (k, v) r) =
    Node3 (fmap f l) (j, f u) (fmap f m) (k, f v) (fmap f r)

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

anoin23 :: Ord k => T23 n k v -> T23 n k v -> I23 n k v
anoin23 Leaf Leaf = Level Leaf
anoin23 (Node2 ai i' im) (Node2 mr r' rz) = case anoin23 im mr of
  Level ir       -> Level (Node3 ai i' ir r' rz)
  Grow2 im m' mr -> Grow2 (Node2 ai i' im) m' (Node2 mr r' rz)
anoin23 (Node2 ai i' im) (Node3 mp p' pu u' uz) = case anoin23 im mp of
  Level ip       -> Grow2 (Node2 ai i' ip) p' (Node2 pu u' uz)
  Grow2 im m' mp -> Grow2 (Node2 ai i' im) m' (Node3 mp p' pu u' uz)
anoin23 (Node3 ag g' gj j' jm) (Node2 mr r' rz) = case anoin23 jm mr of
  Level jr       -> Grow2 (Node2 ag g' gj) j' (Node2 jr r' rz)
  Grow2 jm m' mr -> Grow2 (Node3 ag g' gj j' jm) m' (Node2 mr r' rz)
anoin23 (Node3 ag g' gj j' jm) (Node3 mp p' pu u' uz) = case anoin23 jm mp of
  Level jp       -> Grow2 (Node2 ag g' gj) j' (Node3 jp p' pu u' uz)
  Grow2 jm m' mp -> Grow2 (Node3 ag g' gj j' jm) m' (Node3 mp p' pu u' uz)

data D23 n k v where
  DSame :: T23 n k v -> D23 n k v
  DDrop :: T23 n k v -> D23 (Su n) k v

i2dSu :: I23 n k v -> D23 (Su n) k v
i2dSu (Level t) = DDrop t
i2dSu (Grow2 li i' iu) = DSame (Node2 li i' iu)

dtNode :: D23 n k v -> (k, v) -> T23 n k v -> D23 (Su n) k v
dtNode (DSame am) m' mz                     = DSame (Node2 am m' mz)
dtNode (DDrop am) m' (Node2 mr r' rz)       = DDrop (Node3 am m' mr r' rz)
dtNode (DDrop am) m' (Node3 mp p' ps s' sz) =
  DSame (Node2 (Node2 am m' mp) p' (Node2 ps s' sz))

tdNode :: T23 n k v -> (k, v) -> D23 n k v -> D23 (Su n) k v
tdNode am m' (DSame mz) = DSame (Node2 am m' mz)
tdNode (Node2 af f' fm) m' (DDrop mz) = DDrop (Node3 af f' fm m' mz)
tdNode (Node3 ad d' dh h' hm) m' (DDrop mz) =
  DSame (Node2 (Node2 ad d' dh) h' (Node2 hm m' mz))

delete23 :: Ord k => k -> T23 n k v -> D23 n k v
delete23 k Leaf = DSame Leaf
delete23 k (Node2 ai i' iz) = case compare k (fst i') of
  LT -> dtNode (delete23 k ai) i' iz
  EQ -> i2dSu (anoin23 ai iz)
  GT -> tdNode ai i' (delete23 k iz)
delete23 k (Node3 ai i' ip p' pz) = case (compare k (fst i'), compare k (fst p')) of
  (LT, _) -> case delete23 k ai of
    DSame ai -> DSame (Node3 ai i' ip p' pz)
    DDrop ai -> case ip of
      Node2 im m' mp       ->
        DSame (Node2 (Node3 ai i' im m' mp) p' pz)
      Node3 il l' ln n' np ->
        DSame (Node3 (Node2 ai i' il) l' (Node2 ln n' np) p' pz)
  (EQ, _) -> case anoin23 ai ip of
    Level ap        -> DSame (Node2 ap p' pz)
    Grow2 ai i' ip  -> DSame (Node3 ai i' ip p' pz)
  (_, LT) -> case delete23 k ip of
    DSame ip -> DSame (Node3 ai i' ip p' pz)
    DDrop ip -> case pz of
      Node2 pt t' tz -> DSame (Node2 ai i' (Node3 ip p' pt t' tz))
      Node3 pr r' ru u' uz ->
        DSame (Node3 ai i' (Node2 ip p' pr) r' (Node2 ru u' uz))
  (_, EQ) -> case anoin23 ip pz of
    Level iz        -> DSame (Node2 ai i' iz)
    Grow2 ip p' pz  -> DSame (Node3 ai i' ip p' pz)
  (_, GT) -> case delete23 k pz of
    DSame pz -> DSame (Node3 ai i' ip p' pz)
    DDrop pz -> case ip of
      Node2 im m' mp       ->
        DSame (Node2 ai i' (Node3 im m' mp p' pz))
      Node3 il l' ln n' np ->
        DSame (Node3 ai i' (Node2 il l' ln) n' (Node2 np p' pz))

data Arr (k :: *)(v :: *) where
  Arr :: T23 n k v -> Arr k v
deriving instance (Show k, Show v) => Show (Arr k v)

instance Functor (Arr k) where
  fmap f (Arr t) = Arr (fmap f t)

emptyArr :: Arr k v
emptyArr = Arr Leaf

insertArr :: Ord k => (k, v) -> Arr k v -> Arr k v
insertArr iv (Arr lu) = case insert23 iv lu of
  Level lu       -> Arr lu
  Grow2 lj jv ju -> Arr (Node2 lj jv ju)

findArr :: Ord k => k -> Arr k v -> Maybe v
findArr k (Arr lu) = find23 k lu

deleteArr :: Ord k => k -> Arr k v -> Arr k v
deleteArr k (Arr lu) = case delete23 k lu of
  DSame lu -> Arr lu
  DDrop lu -> Arr lu

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

foldMapSet :: Monoid y => (x -> y) -> Set x -> y
foldMapSet f = foldMapArr (f . fst)

instance (Ord k, Semigroup v) => Semigroup (Arr k v) where (<>) = mappend
instance (Ord k, Semigroup v) => Monoid (Arr k v) where
  mempty = emptyArr
  mappend l r = appEndo (foldMapArr up l) r where
    up (k, v) = Endo $ \ r -> case findArr k r of
      Just w  -> insertArr (k, v <> w) r
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

leftmostArr :: Arr k v -> Maybe k
leftmostArr (Arr t) = go t where
  go :: T23 n k v -> Maybe k
  go Leaf = Nothing
  go (Node2 l (k, _) _) = go l <|> Just k
  go (Node3 l (k, _) _ _ _) = go l <|> Just k

rightmostArr :: Arr k v -> Maybe k
rightmostArr (Arr t) = go t where
  go :: T23 n k v -> Maybe k
  go Leaf = Nothing
  go (Node2 _ (k, _) r) = go r <|> Just k
  go (Node3 _ _ _ (k, _) r) = go r <|> Just k

intersectSet :: Ord x => Set x -> Set x -> Set x
intersectSet xs =
  foldMapArr (\ (y, ()) -> if inSet y xs then singleton y else mempty)

subSet :: Ord x => Set x -> Set x -> Bool
subSet xs ys = getAll (foldMapSet (All . (`inSet` ys)) xs)

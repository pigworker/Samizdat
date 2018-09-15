{-# LANGUAGE GADTs, KindSignatures, DataKinds, TypeOperators, PolyKinds,
    StandaloneDeriving, ScopedTypeVariables #-}

module Circ where

import Data.List
import Data.List.Extra
import Data.Function
import Data.Traversable
import Control.Applicative
import Control.Arrow
import Control.Monad

import BigArray

data Tuply :: * -> * where
  Oney   :: Tuply ()
  Booly  :: Tuply Bool
  (:*:) :: Tuply s -> Tuply t -> Tuply (s, t)
deriving instance Show (Tuply t)
deriving instance Eq (Tuply t)
infixr 4 :*:

class (Show i, Ord i) => TUPLY i where
  tuply :: Tuply i

instance TUPLY () where
  tuply = Oney

instance TUPLY Bool where
  tuply = Booly

instance (TUPLY s, TUPLY t) => TUPLY (s, t) where
  tuply = tuply :*: tuply

tuples :: Tuply t -> [t]
tuples Oney = [()]
tuples Booly = [False, True]
tuples (s :*: t) = (,) <$> tuples s <*> tuples t

data Table :: * -> * -> * where
  Ret   :: x -> Table () x
  Cond  :: x -> x -> Table Bool x
  Curry :: Table s (Table t x) -> Table (s, t) x
deriving instance Show x => Show (Table t x)
deriving instance Eq x => Eq (Table t x)
instance Ord x => Ord (Table t x) where
  compare (Ret x) (Ret y) = compare x y
  compare (Cond x0 y0) (Cond x1 y1) = compare (x0, y0) (x1, y1)
  compare (Curry f) (Curry g) = compare f g

($$) :: Table s x -> s -> x
Ret x    $$ ()      = x
Cond f t $$ False   = f
Cond f t $$ True    = t
Curry f  $$ (s, t)  = f $$ s $$ t
infixl 3 $$

instance Traversable (Table i) where
  traverse f (Ret s)      = Ret <$> f s
  traverse f (Cond s0 s1) = Cond <$> f s0 <*> f s1
  traverse f (Curry st)   = Curry <$> traverse (traverse f) st

instance Foldable (Table i) where foldMap = foldMapDefault
instance Functor (Table i) where fmap = fmapDefault

lambda :: TUPLY s => (s -> x) -> Table s x
lambda = lambdaEx tuply

lambdaEx :: Tuply s -> (s -> x) -> Table s x
lambdaEx Oney      f = Ret (f ())
lambdaEx Booly     f = Cond (f False) (f True)
lambdaEx (s :*: t) f = Curry (lambdaEx s $ \ u -> lambdaEx t $ \ v -> f (u, v))

instance TUPLY i => Applicative (Table i) where
  pure x   = lambda $ \ _ -> x
  f <*> s  = lambda $ \ i -> (f $$ i) (s $$ i)

type Component s i o = Table (s, i) (s, o)

comb :: TUPLY i => (i -> o) -> Component () i o
comb f = lambda $ \ ((), i) -> ((), f i)

(-$) :: Component () i o -> i -> o
f -$ i = snd (f $$ ((), i))

gNAND :: Component () (Bool, Bool) Bool
gNAND = comb $ (not . uncurry (&&))

gDFF :: Component Bool Bool Bool
gDFF = lambda $ \ (q, d) -> (d, q)

gNOT :: Component () Bool Bool
gNOT = comb $ \ b -> gNAND -$ (b, b)

gAND :: Component () (Bool, Bool) Bool
gAND = comb $ \ x -> case x of
  (a, b) -> z where
    c = gNAND -$ (a, b)
    z = gNOT  -$ c

gOR ::  Component () (Bool, Bool) Bool
gOR = comb $ \ x -> case x of
  (a, b) -> z where
    a' = gNOT  -$ a
    b' = gNOT  -$ b
    z  = gNAND -$ (a', b')

gMUX :: Component () (Bool, (Bool, Bool)) Bool
gMUX = comb $ \ x -> case x of
  (c, (b0, b1)) -> z where
    c' = gNOT -$ c
    x  = gAND -$ (c', b0)
    y  = gAND -$ (c,  b1)
    z  = gOR  -$ (x, y)

gJKFF :: Component Bool (Bool, Bool) Bool
gJKFF = lambda $ \ x -> case x of
  (q, (j, k)) -> (q', d') where
    (q', d') = gDFF $$ (q, d)
    k' = gNOT -$ k
    d  = gMUX -$ (q, (j, k'))

gXOR :: Component () (Bool, Bool) Bool
gXOR = comb $ \ x -> case x of
  (a, b) -> z where
    z  = gMUX -$ (a, (b, b'))
    b' = gNOT -$ b

gTFF0 :: Component Bool Bool Bool
gTFF0 = lambda $ \ x -> case x of
  (q, t) -> (q', d') where
    (q', d') = gDFF $$ (q, d)
    d        = gXOR -$ (q, t)

gTFF1 :: Component Bool Bool Bool
gTFF1 = lambda $ \ x -> case x of
  (q, t) -> (q', jk') where
    (q', jk') = gJKFF $$ (q, (t, t))

gCOUNT2 :: Component (Bool, Bool) () (Bool, Bool)
gCOUNT2 = lambda $ \ x -> case x of
  ((q2, q1), ()) -> ((q2', q1'), (t2', t1')) where
    (q1', t1') = gTFF0 $$ (q1, True)
    (q2', t2') = gTFF0 $$ (q2, t1')

gCOUNT3 :: Component (Bool, (Bool, Bool)) () (Bool, (Bool, Bool))
gCOUNT3 = lambda $ \ x -> case x of
  ((q4, (q2, q1)), ()) -> ((q4', (q2', q1')), (t4', (t2', t1'))) where
    (q1', t1') = gTFF0 $$ (q1, True)
    (q2', t2') = gTFF0 $$ (q2, t1')
    (q4', t4') = gTFF0 $$ (q4, t4)
    t4         = gAND  -$ (t2', t1')

gCOUNT2' :: Component (Bool, (Bool, Bool)) () (Bool, Bool)
gCOUNT2' = lambda $ \ x -> case x of
  sv -> (s, t21') where
    (s, (_, t21')) = gCOUNT3 $$ sv


data PART = P | PART :+: PART deriving (Show, Eq)

{-
data PARTy :: PART -> * where
  Py :: PARTy P
  (:++:) :: PARTy p -> PARTy q -> PARTy (p :+: q)
deriving instance Show (PARTy p)
deriving instance Eq (PARTy p)
-}

data Parted :: PART -> * -> * where
  Part :: [x] -> Parted P x
  Sep  :: Parted p x -> Parted q x -> Parted (p :+: q) x
deriving instance Show x => Show (Parted p x)
deriving instance Eq x => Eq (Parted p x)

similar :: Parted p x -> Parted q y -> Bool
similar (Part _) (Part _) = True
similar (Sep a b) (Sep c d) = similar a c && similar b d
similar _ _ = False

data Pos :: PART -> * where
  X :: Pos P
  L :: Pos p -> Pos (p :+: q)
  R :: Pos q -> Pos (p :+: q)
deriving instance Show (Pos p)
deriving instance Eq (Pos p)
instance Ord (Pos p) where
  compare X X = EQ
  compare (L x) (L y) = compare x y
  compare (L x) (R y) = LT
  compare (R x) (L y) = GT
  compare (R x) (R y) = compare x y

unL :: Pos (p :+: q) -> Maybe (Pos p)
unL (L x) = Just x
unL (R y) = Nothing

unR :: Pos (p :+: q) -> Maybe (Pos q)
unR (L y) = Nothing
unR (R x) = Just x

part :: Parted p x -> Pos p -> [x]
part (Part xs) X = xs
part (Sep ps qs) (L x) = part ps x
part (Sep ps qs) (R x) = part qs x

data Partition :: * -> * where
  Partition :: Parted p t -> Table t (Pos p) -> Partition t
  -- invariant: Partition ts f satisfies
  --   elem t (part ts x) = True  <=>  f $$ t = x
deriving instance Show t => Show (Partition t)

allInOne :: TUPLY t => Partition t
allInOne = allInOneEx tuply

allInOneEx :: Tuply t -> Partition t
allInOneEx ty = Partition (Part (tuples ty)) (lambdaEx ty $ \ _ -> X)

refine :: forall t x. (Eq t, Ord x, TUPLY t) => Partition t -> (t -> x) -> Partition t
refine (Partition p f) ob = case refineSub (SubPartition p (Just . (f $$))) ob of
  SubPartition q g -> Partition q (lambda $ \ t -> case g t of Just x -> x)

data SubPartition :: * -> * where
  SubPartition :: Parted p t -> (t -> Maybe (Pos p)) -> SubPartition t
  -- invariant: SubPartition ts f satisfies
  --   elem t (part ts x) = True  <=>  f t = Just x

pairSub :: SubPartition t -> SubPartition t -> SubPartition t
pairSub (SubPartition p f) (SubPartition q g) = SubPartition (Sep p q) $ \ t ->
  L <$> f t <|> R <$> g t

refineSub :: forall t x. (Eq t, Ord x) => SubPartition t -> (t -> x) -> SubPartition t
refineSub (SubPartition (Part ts) f) ob = subPartition (groupSortOn ob ts)
refineSub (SubPartition (Sep p q) f) ob = pairSub
  (refineSub (SubPartition p (unL <=< f)) ob)
  (refineSub (SubPartition q (unR <=< f)) ob)

deal :: [x] -> ([x], [x])
deal [] = ([], [])
deal (x : xs) = (x : zs, ys) where (ys, zs) = deal xs

subPartition :: Eq t => [[t]] -> SubPartition t
subPartition [ts] = SubPartition (Part ts) $ \ t -> if elem t ts then Just X else Nothing
subPartition tss = uncurry pairSub . (subPartition *** subPartition) $ deal tss

analyse :: forall s i o. (Eq s, Ord o, TUPLY s, TUPLY i) => Component s i o -> Partition s
analyse c = iter start where
  start :: Partition s
  start = refine allInOne $ \ s -> lambda $ \ i -> snd (c $$ (s, i))
  iter :: Partition s -> Partition s
  iter x@(Partition p f) = case refine x next of
      y@(Partition q _)
        | similar p q -> y
        | otherwise -> iter y
    where next s = lambda $ \ i -> f $$ (fst (c $$ (s, i)))

data Machine :: * -> * -> * -> * where
  Machine :: TUPLY i =>
    Parted p s -> [(Table i o, [(Pos p, Table i (Pos p))])] -> Machine s i o
instance (Show s, Show o) => Show (Machine s i o) where
  show (Machine p a) = concat ["Machine (", show p, ") (", show a, ")"]

machine :: forall s i o. (Eq s, Ord o, TUPLY s, TUPLY i) =>
           Component s i o -> Machine s i o
machine c = case analyse c of
    Partition p f -> Machine p (foldMapArr (:[]) (go p f))
  where
    go :: Parted p s -> Table s (Pos q) -> Arr (Table i o) [(Pos p, Table i (Pos q))]
    go (Part (s : _)) f = single ( lambda $ \ i -> snd (c $$ (s, i))
                                 , [(X, lambda $ \ i -> f $$ fst (c $$ (s, i)))]
                                 )
    go (Sep p q) f = fmap (fmap (L *** id)) (go p f) <> fmap (fmap (R *** id)) (go q f)

picks :: [x] -> [(x, [x])]
picks [] = []
picks (x : xs) = (x, xs) : [(y, x : ys) | (y, ys) <- picks xs]

mkBisim :: forall b s t i. (Eq b, Ord s, Eq t, TUPLY i) =>
           Arr s t -> [(b, [(s, Table i s)])] -> [(b, [(t, Table i t)])] -> [Arr s t]
mkBisim r [] [] = return r
mkBisim r ((b, sfs) : bsfss) ((b', tgs) : btgss) | b == b' = do
  (r, sfs, tgs) <- precook r sfs tgs
  r <- guess r sfs tgs
  mkBisim r bsfss btgss
  where
    precook r [] tgs = [(r, [], tgs)]
    precook r (sf@(s, f) : sfs) tgs = case findArr s r of
      Nothing -> do
        (r, sfs, tgs) <- precook r sfs tgs
        return (r, sf : sfs, tgs)
      Just t -> case [(g, tgs') | ((t', g), tgs') <- picks tgs] of
        [(g, tgs)] -> do
          r <- foldr ((<=<) . match) return ((,) <$> f <*> g) r
          precook r sfs tgs
        _ -> []
    match :: (s, t) -> Arr s t -> [Arr s t]
    match (s, t) r = case findArr s r of
      Just t' -> if t == t' then return r else []
      Nothing -> return (insertArr (s, t) r)
    guess r [] [] = return r
    guess r ((s, f) : sfs) tgs = do
      ((t, g), tgs) <- picks tgs
      r <- foldr ((<=<) . match) return ((,) <$> f <*> g) r
      (r, sfs, tgs) <- precook (insertArr (s, t) r) sfs tgs
      guess r sfs tgs
mkBisim r _ _ = []

data Bisims :: * -> * -> * -> * -> * where
  Bisims :: (Parted p s, [(Table i o, [(Pos p, Table i (Pos p))])]) ->
            (Parted q t, [(Table i o, [(Pos q, Table i (Pos q))])]) ->
            [Arr (Pos p) (Pos q)] ->
            Bisims s t i o
instance (Show s, Show t, Show o) => Show (Bisims s t i o) where
  show (Bisims lm rm bs) = concat
    ["Bisims (", show lm, ") (", show rm, ") (", show bs, ")"]

bisimulations :: (TUPLY s, TUPLY t, TUPLY i, Ord o) =>
  Component s i o -> Component t i o -> Bisims s t i o
bisimulations c d = case (machine c, machine d) of
  (Machine p lm, Machine q rm) -> Bisims (p, lm) (q, rm) (mkBisim emptyArr lm rm)

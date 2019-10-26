{-# LANGUAGE DeriveFunctor, FlexibleInstances #-}

module Ask where

import Control.Applicative
import Control.Monad
import Control.Monad.Fail

data Ki
  = Ty (Bwd Ki)
  | Si
  deriving (Show, Eq)

newtype Sc x = Sc x deriving (Show, Eq)

data Ty
  = D String [Ty]
  | Ty :> Ty
  | Tup [Ty]
  | All Ki (Sc Ty)
  | Abs (Sc Ty)
  | Int :$ Bwd Ty
  | Gdd Bool Int
  | Any
  deriving (Show, Eq)

data DataType
  = DPar (Ordering, Ki) (Sc DataType)
  | DCons [(String, [Ty])]
  deriving Show

type DataTypes = [(String, DataType)]

data Bwd x = B0 | Bwd x :< x deriving (Show, Eq, Functor)

(<><) :: Bwd x -> [x] -> Bwd x
xz <>< [] = xz
xz <>< (x : xs) = (xz :< x) <>< xs

(<>>) :: Bwd x -> [x] -> [x]
B0 <>> xs = xs
(xz :< x) <>> xs = xz <>> (x : xs)

prj :: Bwd x -> Int -> Either String x
prj B0 _ = Left "missing projection"
prj (_ :< x)  0 = return x
prj (xz :< _) i = prj xz (i - 1)

class Ren t where
  ren :: (Int -> Int) -> t -> t

instance Ren t => Ren (Sc t) where
  ren f (Sc t) = Sc (ren wf t) where
    wf 0 = 0
    wf i = f (i - 1) + 1

instance Ren t => Ren [t] where
  ren = fmap . ren

instance Ren t => Ren (Bwd t) where
  ren = fmap . ren

instance Ren Ty where
  ren f (D d ts)  = D d (ren f ts)
  ren f (s :> t)  = ren f s :> ren f t
  ren f (Tup ts)  = Tup (ren f ts)
  ren f (All k t) = All k (ren f t)
  ren f (Abs t)   = Abs (ren f t)
  ren f (i :$ ts) = f i :$ ren f ts
  ren f (Gdd b i) = Gdd b (f i)
  ren f Any       = Any

isTy :: DataTypes -> Bwd Ki -> Ty -> Either String ()
isTy ds ga (D d ts) = do
  da <- case lookup d ds of
    Just da -> return da
    _ -> Left $ "unknown " ++ d
  dPars ds ga da ts
isTy ds ga (s :> t) = do
  isTy ds ga s
  isTy ds ga t
isTy ds ga (Tup ts) = do
  traverse (isTy ds ga) ts
  return ()
isTy ds ga (All k (Sc t)) = do
  isTy ds (ga :< k) t
isTy ds ga (i :$ tz) = do
  Ty kz <- prj ga i
  myzw (kiTy ds ga) kz tz
  return ()
isTy _ _ _ = Left "not a type"

myzw :: Alternative m => (a -> b -> m c) -> Bwd a -> Bwd b -> m (Bwd c)
myzw f B0 B0 = pure B0
myzw f (az :< a) (bz :< b) = (:<) <$> myzw f az bz <*> f a b
myzw _ _ _ = empty

dPars :: DataTypes -> Bwd Ki -> DataType -> [Ty] -> Either String ()
dPars ds ga (DCons _) [] = return ()
dPars ds ga (DPar (_, k) (Sc da)) (t : ts) = do
  kiTy ds ga k t
  dPars ds ga da ts
dPars _ _ _ _ = Left "invalid data type"

kiTy :: DataTypes -> Bwd Ki -> Ki -> Ty -> Either String ()
kiTy ds ga (Ty kz) t = go ga (kz <>> []) t where
  go ga [] t = isTy ds ga t
  go ga (k : ks) (Abs (Sc t)) = go (ga :< k) ks t
  go _ _ _ = Left "abstraction arity mismatch"
kiTy ds ga Si t = isSi ga t

isSi :: Bwd Ki -> Ty -> Either String ()
isSi _ Any = return ()
isSi ga (Gdd b i) = do
  Si <- prj ga i
  return ()
isSi _ _ = Left "not a size"

subTy :: DataTypes -> Bwd Ki -> (Ty, Ty) -> Either String ()
subTy ds ga (s0 :> t0, s1 :> t1) = do
  subTy ds ga (s1, s0)
  subTy ds ga (t0, t1)
subTy ds ga (D d0 ss, D d1 ts) = do
  guard (d0 == d1)
  da <- case lookup d0 ds of
    Just da -> return da
    _ -> Left $ "unknown " ++ d0
  subPars ds ga da ss ts
subTy ds ga (s, t)
  | s == t = return ()
  | otherwise = Left $ "subTy " ++ show (s, t)

subPars :: DataTypes -> Bwd Ki -> DataType -> [Ty] -> [Ty] -> Either String ()
subPars ds ga (DCons _) [] [] = return ()
subPars ds ga (DPar (o, k) (Sc da)) (s : s0) (t : t0) = do
  case o of
    EQ -> guard (s == t)
    LT -> subKiTy ds ga k s t
    GT -> subKiTy ds ga k t s
  subPars ds ga da s0 t0
subPars _ _ _ _ _ = Left "arity mismatch"

subKiTy :: DataTypes -> Bwd Ki -> Ki -> Ty -> Ty -> Either String ()
subKiTy ds ga Si _ Any = return ()
subKiTy ds ga Si (Gdd a i) (Gdd b j) = do
  guard (i == j)
  guard (a || not b)
subKiTy ds ga Si Any (Gdd _ _) = Left "unguarded"
subKiTy ds ga (Ty kz) s t = go ga (kz <>> []) s t where
  go ga [] s t = subTy ds ga (s, t)
  go ga (k : ks) (Abs (Sc s)) (Abs (Sc t)) = go (ga :< k) ks s t
  go _ _ _ _ = Left "arity mismatch"

class Sbs t where
  sbs, sbw :: (Bwd Ty, Int) -> t -> t
  sbs (B0, _) = id
  sbs sg = sbw sg

instance Sbs t => Sbs (Sc t) where
  sbw (tz, n) (Sc t) = Sc (sbw (tz, n + 1) t)

instance Sbs t => Sbs [t] where
  sbw = fmap . sbw

instance Sbs t => Sbs (Bwd t) where
  sbw = fmap . sbw

instance Sbs Ty where
  sbw sg (D d ts) = D d (sbw sg ts)
  sbw sg (s :> t)  = sbw sg s :> sbw sg t
  sbw sg (Tup ts)  = Tup (sbw sg ts)
  sbw sg (All k t) = All k (sbw sg t)
  sbw sg (Abs t)   = Abs (sbw sg t)
  sbw sg@(_, n) (i :$ sz) | i < n = i :$ sbw sg sz
  sbw sg@(tz, n) (i :$ sz) = go tz (i - n) (sbw sg sz) where
    go B0 i uz = (i + n) :$ uz
    go (_ :< t) 0 uz = app (if n == 0 then t else ren (n +) t) uz
    go (tz :< _) i uz = go tz (i - 1) uz
    app (Abs (Sc t)) uz = app t uz
    app t uz = sbs (uz, 0) t
  sbw (_, n) (Gdd b i) | i < n = Gdd b i
  sbw (tz, n) (Gdd b i) = go tz (i - n) where
    go B0 i = Gdd b (i + n)
    go (_ :< t) 0 = case t of
      Any      -> Any
      Gdd c j  -> Gdd (b || c) j
    go (tz :< _) i = go tz (i - 1)
  sbw sg Any       = Any

data Tm
  = E El
  | A (Sc Tm)
  | L Tm
  | Int :! [Tm]
  deriving Show

data El
  = X Int
  | Tm ::: Ty
  | El :/ Ty
  | El :- Tm
  | El :. Int
  | El :? (Ty, [Tm])
  | El :* (Ty, Tm)
  deriving Show


daCons :: DataType -> [Ty] -> Either String [(String, [Ty])]
daCons da ts = go B0 da ts where
  go tz (DCons css) [] = do
    return [(c, sbs (tz, 0) s) | (c, s) <- css]
  go tz (DPar _ (Sc da)) (t : ts) = go (tz :< t) da ts
  go _ _ _ = Left "bad data type"

chk :: DataTypes -> Bwd Ki -> Bwd Ty -> Ty -> Tm -> Either String ()
chk ds ga de tT (E e) = do
  sS <- syn ds ga de e
  subTy ds ga (sS, tT)
chk ds ga de (All k (Sc tT)) (A (Sc t)) = do
  chk ds (ga :< k) de tT t
chk ds ga de (sS :> tT) (L t) = do
  chk ds ga (de :< sS) tT t
chk ds ga de (Tup tTs) (0 :! ts) = chks ds ga de tTs ts
chk ds ga de (D d (Any : sSs)) (i :! ts) = do
  da <- case lookup d ds of
    Just da -> return da
    _ -> Left $ "unknown " ++ d
  cTs <- daCons da (Any : sSs)
  guard (i < length cTs)
  chks ds ga de (snd (cTs !! i)) ts
chk _ ga de tT t = Left $ "chk" ++ show (ga, de, tT, t)

chks :: DataTypes -> Bwd Ki -> Bwd Ty -> [Ty] -> [Tm] -> Either String ()
chks ds ga de [] [] = return ()
chks ds ga de (tT : tTs) (t : ts) = do
    chk  ds ga de tT t
    chks ds ga de tTs ts
chks _ _ _ _ _  = Left "length mismatch"

cases :: DataTypes -> Bwd Ki -> Bwd Ty ->
  [(String, [Ty])] -> Ty -> [Tm] -> Either String ()
cases _ _ _ [] _ [] = return ()
cases ds ga de ((_, sSs) : cTs) tT (t : ts) = do
  chk ds ga (de <>< sSs) tT t
  cases ds ga de cTs tT ts
cases _ _ _ _ _ _ = Left "wrong number of cases"

syn :: DataTypes -> Bwd Ki -> Bwd Ty -> El -> Either String Ty
syn ds ga de (X i) = prj de i
syn ds ga de (t ::: tT) = do
  isTy ds ga tT
  chk ds ga de tT t
  return tT
syn ds ga de (f :/ sS) = do
  All k (Sc tT) <- syn ds ga de f
  kiTy ds ga k sS
  return (sbs (B0 :< sS, 0) tT)
syn ds ga de (f :- s) = do
  sS :> tT <- syn ds ga de f
  chk ds ga de sS s
  return tT
syn ds ga de (e :. i) = do
  Tup tTs <- syn ds ga de e
  guard (i < length tTs)
  return (tTs !! i)
syn ds ga de (e :? (tT, ts)) = do
  D d sSs <- syn ds ga de e
  da <- case lookup d ds of
    Just da -> return da
    _ -> Left $ "unknown " ++ d
  cTs <- daCons da sSs
  cases ds ga de cTs tT ts
  return tT
syn ds ga de (e :* (tT, t)) = do
  D d (Any : sSs) <- syn ds ga de e
  let sSs' = ren (1 +) sSs
  let gD b = D d (Gdd b 0 : sSs')
  let tT' = ren (1 +) tT
  chk ds ga de (All Si (Sc ((gD True :> tT') :> (gD False :> tT')))) t
  return tT

data Va
  = Bwd Va :\: Tm
  | Int :!: [Va]
  | Mu Va
  deriving Show

evTm :: Bwd Va -> Tm -> Va
evTm rh (E e) = evEl rh e
evTm rh (A (Sc t)) = evTm rh t
evTm rh (L t) = rh :\: t
evTm rh (i :! ts) = i :!: fmap (evTm rh) ts

evEl :: Bwd Va -> El -> Va
evEl rh (X i) = case prj rh i of
  Right v -> v
evEl rh (t ::: _) = evTm rh t
evEl rh (e :/ _) = evEl rh e
evEl rh (f :- s) = apply (evEl rh f) (evTm rh s)
evEl rh (e :. i) = case evEl rh e of
  _ :!: vs -> vs !! i
evEl rh (e :? (_, ts)) = case evEl rh e of
  i :!: vs -> evTm (rh <>< vs) (ts !! i)
evEl rh (e :* (tT, t)) = apply (Mu (evTm rh t)) (evEl rh e)

apply :: Va -> Va -> Va
apply (rh :\: t) s = evTm (rh :< s) t
apply r@(Mu f) v@(i :!: ts) = apply (apply f r) v

myNat :: (String, DataType)
myNat = (,) "Nat" $
  DPar (LT, Si) . Sc $
  DCons
    [ ("Z", [])
    , ("S", [D "Nat" [Gdd True 0]])
    ]

myPlus :: Tm
myPlus = L (L (E (X 1 :* (D "Nat" [Any],
  A (Sc (L (L (E (X 0 :? (D "Nat" [Any],
    [ E (X 2)
    , 1 :! [E (X 2 :- E (X 0))]
    ]))))
  ))))))

tyPlus :: Ty
tyPlus = D "Nat" [Any] :> (D "Nat" [Any] :> D "Nat" [Any])

myTwo :: Tm
myTwo = 1 :! [1 :! [0 :! []]]

myTest :: El
myTest = ((myPlus ::: tyPlus) :- myTwo) :- myTwo

myBadPlus :: Tm
myBadPlus = L (L (E (X 1 :* (D "Nat" [Any],
  A (Sc (L (L (E (X 3 :? (D "Nat" [Any],
    [ E (X 2)
    , 1 :! [E (X 2 :- E (X 0))]
    ]))))
  ))))))

instance MonadFail (Either String) where
  fail = Left

instance Alternative (Either String) where
  empty = Left "it went wrong"
  Left e <|> r = r
  r <|> _ = r
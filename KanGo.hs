{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,
    GADTs, DataKinds, KindSignatures, TypeOperators,
    TypeFamilies, TupleSections, PolyKinds, RankNTypes,
    MultiParamTypeClasses, FlexibleInstances, ScopedTypeVariables #-}

module KanGo where

import Control.Monad
import Control.Monad.Identity
import Control.Applicative

data SC = TM | EL | PT

data CX = C0 | CX :\ SC

data Var :: CX -> SC -> * where
  V0 :: Var (g :\ s) s
  VS :: Var g t -> Var (g :\ s) t

data Quant = Pi | Sg deriving (Show, Eq)
data Bit = B0 | B1 deriving (Show, Eq)

data Syn :: CX -> SC -> * where
  I      :: Bit -> Syn g PT
  Mux    :: Syn g PT -> Syn g PT -> Syn g PT -> Syn g PT

  Type   :: Syn g TM
  
  B      :: Quant -> Syn g TM -> Bnd g EL -> Syn g TM
  L      :: Bnd g EL -> Syn g TM
  (:&)   :: Syn g TM -> Syn g TM -> Syn g TM

  (:-:)  :: Syn g TM -> Syn g TM -> Syn g TM
  Path   :: Bnd g PT -> Syn g TM
  KanT   :: Triple (Syn g TM) -> Triple (Syn g TM) -> Syn g TM ->
            (Syn g PT, Syn g PT) -> Syn g TM

  E      :: Syn g EL -> Syn g TM

  V      :: Var g c -> Syn g c
  P      :: FV c -> Syn g c

  (:::)  :: Syn g TM -> Syn g TM -> Syn g EL

  (:$)   :: Syn g EL -> Syn g TM -> Syn g EL
  (:.)   :: Syn g EL -> Syn g PT -> Syn g EL
  (:@)   :: Syn g EL -> Bit -> Syn g EL
  (:^)   :: Syn g TM -> Syn g EL -> Syn g EL

data Bnd :: CX -> SC -> * where
  R :: Syn (g :\ b) TM -> Bnd g b
  K :: Syn g TM -> Bnd g b

bnd :: Syn (g :\ b) TM -> Bnd g b
bnd t = case dep b of
    Left t  -> K t
    Right _ -> b
  where b = R t
  -- could add thickening?

class Kit (t :: CX -> SC -> *) where
  vze   :: t (g :\ b) b
  tout  :: t g b -> Syn g b
  wk    :: t g b -> t (g :\ c) b

instance Kit Var where
  vze   = V0
  tout  = V
  wk    = VS

instance Kit Syn where
  vze   = V V0
  tout  = id
  wk    = ren VS

act :: (Applicative f, Kit t) => (forall b. Var g b -> f (t d b)) ->
       Syn g b -> f (Syn d b)
act f (I b)       = pure (I b)
act f (Mux r s t) = Mux <$> act f r <*> act f s <*> act f t
act f Type        = pure Type
act f (B q s t)   = B q <$> act f s <*> bact f t
act f (L t)       = L <$> bact f t
act f (s :& t)    = (:&) <$> act f s <*> act f t
act f (s :-: t)   = (:-:) <$> act f s <*> act f t
act f (Path t)    = Path <$> bact f t
act f (KanT (Tr s0 sq s1) (Tr t0 tq t1) st (p, q)) =
  KanT <$> (Tr <$> act f s0 <*> act f sq <*> act f s1)
       <*> (Tr <$> act f t0 <*> act f tq <*> act f t1)
       <*> act f sq
       <*> ((,) <$> act f p <*> act f q)

bact :: forall f t g d c. (Applicative f, Kit t) =>
       (forall b. Var g b -> f (t d b)) ->
       Bnd g c -> f (Bnd d c)
bact f (R t) = R <$> act g t where
  g :: forall b. Var (g :\ c) b -> f (t (d :\ c) b)
  g V0 = pure vze
  g (VS i) = wk <$> f i
bact f (K t) = K <$> act f t

ren :: (forall b. Var g b -> Var d b) -> Syn g b -> Syn d b
ren f = runIdentity . act (Identity . f)

dep :: Bnd g b -> Either (Syn g TM) (Syn (g :\ b) TM)
dep (K t) = Left t
dep (R t) = case act str t of
    Just t  -> Left t
    Nothing -> Right t
  where
    str :: Var (g :\ b) c -> Maybe (Var g c)
    str V0     = Nothing
    str (VS i) = Just i

data Sem :: SC -> * where
  VI     :: Bit -> Sem PT
  VMux   :: FV PT -> Sem PT -> Sem PT -> Sem PT

  VType  :: Sem TM
  
  VB     :: Quant -> Sem TM -> Clo EL -> Sem TM
  VL     :: Clo EL -> Sem TM
  (::&)  :: Sem TM -> Sem TM -> Sem TM

  (::-:) :: Sem TM -> Sem TM -> Sem TM
  VPath  :: Clo PT -> Sem TM
  VKanT  :: Triple (Sem TM) -> Triple (Sem TM) -> Sem TM ->
            (Sem PT, Sem PT) -> Sem TM

  N      :: Sem EL -> Sem TM

  X      :: FV EL -> Sem EL

  (::$)  :: Sem EL -> Sem TM -> Sem EL
  (::.)  :: Sem EL -> Sem PT -> Sem EL
  (::@)  :: Sem EL -> Bit -> Sem EL
  XP     :: Triple (Sem TM) -> Sem TM -> Sem EL

data Clo :: SC -> * where
  VR :: Env g -> Syn (g :\ b) TM -> Clo b
  VK :: Sem TM -> Clo b

stan :: Clo b -> Val b -> Int -> Val TM
stan (VR g b) v = eval (g :< v) b
stan (VK t) _   = pure t

data Env :: CX -> * where
  E0   :: Env C0
  (:<) :: Env g -> Val b -> Env (g :\ b)

type family Val (c :: SC) :: * where
  Val PT = Sem PT
  Val EL = (Sem TM, Sem TM)
  Val TM = Sem TM

data FV :: SC -> * where
  Dim :: Int -> FV PT
  Par :: Int -> Sem TM -> FV EL

instance Eq (FV c) where
  Dim i   == Dim j    = i == j
  Par i _ == Par j _  = i == j

dim :: FV PT -> Val PT
dim i = VMux i (VI B0) (VI B1)

eval :: Env g -> Syn g b -> Int -> Val b
eval _ (I b) = pure (VI b)
eval g (Mux c p0 p1) = mux <$> eval g c <*> eval g p0 <*> eval g p1
eval _ Type  = pure VType
eval g (B q s t) = VB q <$> eval g s <*> clo g t
eval g (L b) = VL <$> clo g b
eval g (s :& t) = (::&) <$> eval g s <*> eval g t
eval g (s :-: t) = (::-:) <$> eval g s <*> eval g t
eval g (Path b) = VPath <$> clo g b
eval g (KanT sT tT st (i, j)) =
  join (kan <$> traverse (eval g) sT <*> traverse (eval g) tT <*> eval g st
            <*> ((,) <$> eval g i <*> eval g j))
eval g (E e) = fst <$> eval g e
eval g (V i) = pure (proj g i)
eval _ (P i@(Dim _)) = pure (dim i)
eval _ (P x@(Par i t)) = pure (N (X x), t)
eval g (f :$ s) = join (apf <$> eval g f <*> eval g s)
eval g (f :. s) = (, VType) <$> join (apa <$> eval g f <*> eval g s)
eval g (e :@ b) = join (field b <$> eval g e)
eval g (r :^ q) = join (transport <$> eval g r <*> eval g q)

lam :: Sem TM -> (Sem TM -> Int -> Sem TM) -> Int -> Sem TM
lam (VB Pi vS cT) f = underEL vS $ \ x -> do
  let vx = N (X x)
  vt <- f vx
  vT <- stan cT (vx, vS)
  tT <- quote (Q0 :\\ x) vT vt
  VL <$> clo E0 (bnd tT)

path :: (Sem PT -> Int -> Sem TM) -> Int -> Sem TM
path p = underPT $ \ i -> do
  vT <- p (dim i)
  tT <- quote (Q0 :\\ i) VType vT
  VPath <$> clo E0 (bnd tT)

transport :: Val TM -> Val EL -> Int -> Val EL
transport vr (VPath (VK vR), _) = pure (vr, vR)
transport vr (vq, vQ@(vR ::-: vU)) = do
  q <- quote Q0 vQ vq
  case q of
    Path b  -> case dep b of
      Left _   -> pure (vr, vR)
      Right rR -> (, vU) <$> case (vr, rR) of
        (_, B Sg sS tT) -> do
          let vS i = eval (E0 :< i) sS
          (vs0, vS0) <- field B0 (vr, vR)
          let vs i = do
                vSi <- vS i
                qS <- path $ \ j -> vS (mux j (VI B0) i)
                fst <$> transport vs0 (qS, vS0 ::-: vSi)
              vT i = do
                cT <- clo (E0 :< i) tT
                stan cT =<< ((,) <$> vs i <*> vS i)
          (vt0, vT0) <- field B1 (vr, vR)
          vT1 <- vT (VI B1)
          qT <- path vT
          (::&) <$> vs (VI B1) <*> (fst <$> transport vt0 (qT, vT0 ::-: vT1))
        (_, B Pi sS tT) -> lam vU $ \ vs1 -> do
          let vS i = eval (E0 :< i) sS
              vs i = do
                vSS <- (::-:) <$> vS (VI B1) <*> vS i
                qS <- path $ \j -> vS (mux j (VI B1) i)
                fst <$> transport vs1 (qS, vSS)
              vT i = do
                cT <- clo (E0 :< i) tT
                stan cT =<< ((,) <$> vs i <*> vS i)
          (vt0, vT0) <- apf (vr, vR) =<< vs (VI B0)
          vT1 <- vT (VI B1)
          qT <- path vT
          fst <$> transport vt0 (qT, vT0 ::-: vT1)
        (_, sS :-: tT) -> path $ \ j -> do
            let vS i = eval (E0 :< i) sS
                vT i = eval (E0 :< i) tT
            vST <- Tr <$> vS (VI B0) <*> path vS <*> vS (VI B1)
            vTT <- Tr <$> vT (VI B0) <*> path vT <*> vT (VI B1)
            kan vST vTT vr (VI B1, j)
        _ -> pure (N (XP (Tr vR vq vU) vr))

data Triple x = Tr x x x deriving (Functor, Foldable, Traversable)

degenerate :: Triple (Sem TM) -> Int -> Bool
degenerate (Tr vS0 qS vS1) = underPT $ \ i -> do
  vS <- apa (qS, vS0 ::-: vS1) (dim i)
  sS <- quote (Q0 :\\ i) VType vS
  case bnd sS of
    K _  -> pure True
    R _ -> pure False

kan :: Triple (Sem TM) -> Triple (Sem TM) -> Sem TM -> (Sem PT, Sem PT) ->
       Int -> Sem TM
kan (Tr vS0 _ _) (Tr vT0 _ _) st0 (VI B0, j) = apa (st0, vS0 ::-: vT0) j
kan (Tr vS0 vS1 qS) _ _ (i, VI B0) = apa (qS, vS0 ::-: vS1) i
kan _ (Tr vT0 vT1 qT) _ (i, VI B1) = apa (qT, vT0 ::-: vT1) i
kan s3@(Tr vS0 _ _) t3@(Tr vT0 _ _) st0 (i, j) = do
  b <- (&&) <$> degenerate s3 <*> degenerate t3
  if b then apa (st0, vS0 ::-: vT0) j else pure $ VKanT s3 t3 st0 (i, j)

field :: Bit -> Val EL -> Int -> Val EL
field B0 (s ::& _, VB Sg sS _)  = pure (s,            sS)
field B0 (N e,     VB Sg sS _)  = pure (N (e ::@ B0), sS)
field B1 (s ::& t, VB Sg sS tT) = (t,) <$> stan tT (s, sS)
field B1 (N e,     VB Sg sS tT) = (N (e ::@ B1),) <$> stan tT (N (e ::@ B0), sS)

apa :: Val EL -> Val PT -> Int -> Sem TM
apa (_, sS ::-: tT) (VI B0) = pure sS
apa (_, sS ::-: tT) (VI B1) = pure tT
apa (VPath b, _) i = stan b i
apa (N f, _) i     = pure (N (f ::. i))

apf :: Val EL -> Val TM -> Int -> Val EL
apf (f, VB Pi sS tT) s =
  let vs = (s, sS)
      vT = stan tT vs
      vt = case f of
             VL b -> stan b vs
             N f  -> pure (N (f ::$ s))
  in  (,) <$> vt <*> vT
  
proj :: Env g -> Var g b -> Val b
proj (_ :< v) V0 = v
proj (g :< _) (VS i) = proj g i

clo :: Env g -> Bnd g b -> Int -> Clo b
clo g (R b) = pure (VR g b)
clo g (K t) = VK <$> eval g t

mux :: Sem PT -> Sem PT -> Sem PT -> Sem PT
mux (VI B0) p0 _ = p0
mux (VI B1) _ p1 = p1
mux (VMux i q0 q1) p0 p1 = vmux i (mux q0 p0 p1) (mux q1 p0 p1)

vmux :: FV PT -> Sem PT -> Sem PT -> Sem PT
vmux i p0 p1 | pteq p0 p1 = p0
vmux (Dim i) (VMux (Dim j) q0 q1) p1
  | i == j  = vmux (Dim i) q0 p1
  | i < j   = vmux (Dim j) (vmux (Dim i) q0 p1) (vmux (Dim i) q1 p1)
vmux (Dim i) p0 (VMux (Dim j) q0 q1)
  | i == j  = vmux (Dim i) p0 q1
  | i < j   = vmux (Dim j) (vmux (Dim i) p0 q0) (vmux (Dim i) p0 q1)

pteq :: Sem PT -> Sem PT -> Bool
pteq (VI b) (VI c) = b == c
pteq (VMux i p0 p1) (VMux j q0 q1) =
  i == j && pteq p0 q0 && pteq p1 q1

data QJ :: CX -> * where
  Q0 :: QJ C0
  (:\\) :: QJ g -> FV b -> QJ (g :\ b)

data (:~:) :: t -> t -> * where
  Refl :: t :~: t

fveq :: FV a -> FV b -> Maybe (a :~: b)
fveq (Dim i) (Dim j) | i == j = Just Refl
fveq (Par i _) (Par j _) | i == j = Just Refl
fveq _ _ = Nothing

dbFV :: QJ g -> FV b -> Maybe (Var g b)
dbFV Q0 _ = Nothing
dbFV (q :\\ x) y = case fveq x y of
  Just Refl -> pure V0
  _         -> VS <$> dbFV q y

underEL :: Sem TM -> (FV EL -> Int -> x) -> Int -> x
underEL vS k i = k (Par i vS) (i + 1)

underPT :: (FV PT -> Int -> x) -> Int -> x
underPT k i = k (Dim i) (i + 1)

quote :: QJ g -> Sem TM -> Sem TM -> Int -> Syn g TM
quote q VType VType         = pure Type
quote q VType (VB z vS cT)  = B z <$> quote q VType vS <*>
  (underEL vS $ \ x -> do
    vx <- eval E0 (P x)
    vT <- stan cT vx
    bnd <$> quote (q :\\ x) VType vT)
quote q VType (VKanT vST@(Tr vS0 _ _) vTT@(Tr vT0 _ _) vst0 (vi, vj)) =
  KanT <$> quotr q vST <*> quotr q vTT <*> quote q (vS0 ::-: vT0) vst0
       <*> pure (quopt q vi, quopt q vj)
quote q vF@(VB Pi vS cT) vf = underEL vS $ \ x -> do
    (vt, vT) <- apf (vf, vF) (N (X x))
    L <$> (bnd <$> quote (q :\\ x) vT vt)
quote q vP@(VB Sg vS cT) vp = do
  (vs, vS) <- field B0 (vp, vP)
  (vt, vT) <- field B1 (vp, vP)
  (:&) <$> quote q vS vs <*> quote q vT vt
quote q vQ@(vS ::-: vT) vq = underPT $ \ i -> do
  vi <- eval E0 (P i)
  vS <- apa (vq, vQ) vi
  Path <$> (bnd <$> quote (q :\\ i) VType vS)
quote q _ (N e) = E <$> (fst <$> quoel q e)

quotr :: QJ g -> Triple (Sem TM) -> Int -> Triple (Syn g TM)
quotr q (Tr vS0 qS vS1) =
  Tr <$> quote q VType vS0 <*> quote q (vS0 ::-: vS1) qS <*> quote q VType vS1

quoel :: QJ g -> Sem EL -> Int -> (Syn g EL, Sem TM)
quoel q (X x@(Par _ vT)) = case dbFV q x of
  Just i   -> pure (V i, vT)
  Nothing  -> pure (P x, vT)
quoel q (vf ::$ vs) = do
  (f, VB Pi vS cT) <- quoel q vf
  (,) <$> ((f :$) <$> quote q vS vs)
      <*> stan cT (vs, vS)
quoel q (vf ::. vp) = do
  (f, vS ::-: vT) <- quoel q vf
  pure $ (f :. quopt q vp, VType)
quoel q (ve ::@ b) = do
  (e, vE@(VB Sg vS cT)) <- quoel q ve
  (_, vT) <- field b (N ve, vE)
  pure (e :@ b, vT)

quopt :: QJ g -> Sem PT -> Syn g PT
quopt q (VI b) = I b
quopt q (VMux x p0 p1) = Mux p (quopt q p0) (quopt q p1) where
  p = case dbFV q x of
        Just i   -> V i
        Nothing  -> P x


  



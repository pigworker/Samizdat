{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,
    GADTs, DataKinds, KindSignatures, TypeOperators,
    TypeFamilies, TupleSections, PolyKinds, RankNTypes,
    MultiParamTypeClasses, FlexibleInstances, ScopedTypeVariables,
    StandaloneDeriving, FlexibleContexts, UndecidableInstances #-}

module KanGo where

import Control.Monad
import Control.Monad.Identity
import Control.Applicative
import Data.Maybe

data SC  -- syntactic categories
   = TM  -- terms (checkable)
   | EL  -- eliminations (synthable)
   | PT  -- points

data CX  -- contexts expose the syntactic categories of bound vars
   = C0
   | CX :\ SC

data Var :: CX -> SC -> * where  -- de Bruijn indices for bound vars
  V0 :: Var (g :\ s) s
  VS :: Var g t -> Var (g :\ s) t
deriving instance Eq (Var g s)

data Syn :: CX -> SC -> * where
  I      :: Bit -> Syn g PT
  Mux    :: Syn g PT -> Syn g PT -> Syn g PT -> Syn g PT

  Type   :: Syn g TM
  
  B      :: Quant -> Syn g TM -> Bnd g EL -> Syn g TM
  L      :: Bnd g EL -> Syn g TM
  (:&)   :: Syn g TM -> Syn g TM -> Syn g TM

  (:-:)  :: Syn g TM -> Syn g TM -> Syn g TM
  Conn   :: Syn g TM -> Triple (Syn g TM) -> Syn g TM -> Syn g TM
  Path   :: Bnd g PT -> Syn g TM
  KanT   :: KAN (Syn g) -> Syn g TM
  Inter  :: INTERPOL (Syn g) -> Syn g TM

  E      :: Syn g EL -> Syn g TM

  V      :: Var g c -> Syn g c
  P      :: FV c -> Syn g c

  (:::)  :: Syn g TM -> Syn g TM -> Syn g EL

  (:$)   :: Syn g EL -> Syn g TM -> Syn g EL
  (:.)   :: Syn g EL -> Syn g PT -> Syn g EL
  (:@)   :: Syn g EL -> Bit -> Syn g EL
  (:^)   :: Syn g TM -> Triple (Syn g TM) -> Syn g EL
  KanV   :: Bit -> KAN (Syn g) -> Syn g TM -> Syn g EL
  InterV :: Bit -> INTERPOL (Syn g) -> Syn g TM -> Syn g EL
deriving instance Eq (Syn g b)

data Bnd :: CX -> SC -> * where
  R :: Nom -> Syn (g :\ b) TM -> Bnd g b   -- relevant
  K :: Syn g TM -> Bnd g b                    -- konstant
  deriving Eq

newtype Nom = Nom {nom :: String}
instance Show Nom where show = nom
instance Eq Nom where _ == _ = True

data Quant = Pi | Sg deriving Eq
instance Show Quant where
  show Pi = "->"
  show Sg = "*"

data Bit = B0 | B1 deriving Eq  -- I probably use these for too much
instance Show Bit where
  show B0 = "0"
  show B1 = "1"

data Pair x = Pr {
  thing0 :: x    ,
  thing1 :: x    }
  deriving (Functor, Foldable, Traversable, Eq)
thing :: Bit -> Pair x -> x
thing B0 = thing0
thing B1 = thing1

data Triple x = Tr  {
  point0 :: x       ,
  path01 :: x       ,
  point1 :: x       }
  deriving (Functor, Foldable, Traversable, Eq)
  -- to be used for two things joined by a path in the middle
point :: Bit -> Triple x -> x
point B0 = point0
point B1 = point1

data KAN f = KAN            {
  side0   :: Triple (f TM)  ,
  side1   :: Triple (f TM)  ,
  base    :: f TM           ,
  vert    :: f PT           ,
  horiz   :: f PT           }
deriving instance Eq (KAN (Syn g))
side :: Bit -> KAN f -> Triple (f TM)
side B0 = side0
side B1 = side1

data INTERPOL f = INTERPOL {
  types  :: Pair (f TM)    ,  -- S                           T
  xports :: Pair (f TM)    ,  -- f : S -> T                  g : T -> S
  rtrips :: Pair (f TM)    ,  -- p : (s : S) -> f (g s) = s  q : (t : T) -> g (f t) = t
  triang :: Pair (f TM)    ,  -- (s : S) -> q (f s) = \ i -> g (p s i)
  coord  :: f PT           }  --                  (t : T) -> p (g t) = \ i -> f (q t i)
deriving instance Eq (INTERPOL (Syn g))

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
act f (I b)          = pure (I b)
act f (Mux r s t)    = Mux <$> act f r <*> act f s <*> act f t
act f Type           = pure Type
act f (B q s t)      = B q <$> act f s <*> bact f t
act f (L t)          = L <$> bact f t
act f (s :& t)       = (:&) <$> act f s <*> act f t
act f (s :-: t)      = (:-:) <$> act f s <*> act f t
act f (Conn s q t)   = Conn <$> act f s <*> traverse (act f) q <*> act f t
act f (Path t)       = Path <$> bact f t
act f (KanT k)       = KanT <$> kact f k
act f (Inter i)      = Inter <$> iact f i
act f (E e)          = E <$> act f e
act f (V i)          = tout <$> f i
act f (P x)          = pure (P x)
act f (g :$ s)       = (:$) <$> act f g <*> act f s
act f (g :. p)       = (:.) <$> act f g <*> act f p
act f (g :@ b)       = (:@) <$> act f g <*> pure b
act f (g :^ q)       = (:^) <$> act f g <*> traverse (act f) q
act f (KanV b k v)   = KanV b <$> kact f k <*> act f v
act f (InterV b i v) = InterV b <$> iact f i <*> act f v

kact :: (Applicative f, Kit t) => (forall b. Var g b -> f (t d b)) ->
        KAN (Syn g) -> f (KAN (Syn d))
kact f (KAN s0 s1 b v h) =
  KAN <$> traverse (act f) s0 <*> traverse (act f) s1 <*> act f b
      <*> act f v <*> act f h

iact :: (Applicative f, Kit t) => (forall b. Var g b -> f (t d b)) ->
        INTERPOL (Syn g) -> f (INTERPOL (Syn d))
iact f (INTERPOL st fg pq hk i) =
  INTERPOL <$> traverse (act f) st <*> traverse (act f) fg
           <*> traverse (act f) pq <*> traverse (act f) hk
           <*> act f i

bact :: forall f t g d c. (Applicative f, Kit t) =>
       (forall b. Var g b -> f (t d b)) ->
       Bnd g c -> f (Bnd d c)
bact f (R x t) = R x <$> act g t where
  g :: forall b. Var (g :\ c) b -> f (t (d :\ c) b)
  g V0 = pure vze
  g (VS i) = wk <$> f i
bact f (K t) = K <$> act f t

ren :: (forall b. Var g b -> Var d b) -> Syn g b -> Syn d b
ren f = runIdentity . act (Identity . f)

dep :: Bnd g b -> Either (Syn g TM) (Syn (g :\ b) TM)
dep (K t)   = Left t
dep (R x t) = case act str t of
    Just t  -> Left t
    Nothing -> Right t
  where
    str :: Var (g :\ b) c -> Maybe (Var g c)
    str V0     = Nothing
    str (VS i) = Just i

bnd :: String -> Syn (g :\ b) TM -> Bnd g b
bnd x t = case dep b of
    Left t  -> K t
    Right _ -> b
  where b = R (Nom x) t
  -- could add thickening?

data Sem :: SC -> * where
  VI      :: Bit -> Sem PT
  VMux    :: FV PT -> Sem PT -> Sem PT -> Sem PT

  VType   :: Sem TM
  
  VB      :: Quant -> Sem TM -> Clo EL -> Sem TM
  VL      :: Clo EL -> Sem TM
  (::&)   :: Sem TM -> Sem TM -> Sem TM

  (::-:)  :: Sem TM -> Sem TM -> Sem TM
  VConn   :: Sem TM -> Triple (Sem TM) -> Sem TM -> Sem TM
  VPath   :: Clo PT -> Sem TM
  VKanT   :: KAN Sem -> Sem TM
  VInter  :: INTERPOL Sem -> Sem TM

  N       :: Sem EL -> Sem TM

  X       :: FV EL -> Sem EL

  (::$)   :: Sem EL -> Sem TM -> Sem EL
  (::.)   :: Sem EL -> Sem PT -> Sem EL
  (::@)   :: Sem EL -> Bit -> Sem EL
  (::^)   :: Sem TM -> Triple (Sem TM) -> Sem EL
  VKanV   :: Bit -> KAN Sem -> Sem TM -> Sem EL
  VInterV :: Bit -> INTERPOL Sem -> Sem TM -> Sem EL

data Env :: CX -> * where
  E0   :: Env C0
  (:<) :: Env g -> Val b -> Env (g :\ b)

data Clo :: SC -> * where
  VR :: Env g -> Nom -> Syn (g :\ b) TM -> Clo b  -- relevant
  VK :: Sem TM -> Clo b                              -- konstant

data FV :: SC -> * where
  Dim :: Int -> Nom -> FV PT
  Par :: Int -> Sem TM -> Nom -> FV EL

nomC :: Clo b -> String
nomC (VR _ x _) = nom x
nomC _ = "x"


-- Semantically, this is what we expect to get when
-- we eval whatever it is.

type family Val (c :: SC) :: * where
  Val PT = Sem PT
  Val EL = (Sem TM, Sem TM)  -- (val, type)
  Val TM = Sem TM

-- semantically, everything needs a name supply;
-- we work in (Int ->)

stan :: Clo b -> Val b -> Int -> Val TM
stan (VR g _ b) v = eval (g :< v) b
stan (VK t)     _ = pure t

instance Ord (FV PT) where
  compare (Dim i _) (Dim j _) = compare i j

instance Eq (FV c) where
  Dim i _   == Dim j _    = i == j
  Par i _ _ == Par j _ _  = i == j

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
eval g (Conn s q t) = VConn <$> eval g s <*> traverse (eval g) q <*> eval g t
eval g (Path b) = VPath <$> clo g b
eval g (KanT k) = kan =<< keval g k
eval g (Inter i) = inter =<< ieval g i
eval g (E e) = fst <$> eval g e
eval g (V i) = pure (proj g i)
eval _ (P i@(Dim _ _)) = pure (dim i)
eval _ (P x@(Par i t _)) = pure (N (X x), t)
eval g (t ::: tT) = (,) <$> eval g t <*> eval g tT
eval g (f :$ s) = join (apf <$> eval g f <*> eval g s)
eval g (f :. p) = do
  qQ@(vq, vQ) <- eval g f
  vp <- eval g p
  case vQ of
    vS ::-: vT -> (, VType) <$> apa (Tr vS vq vT) vp
    VConn vs vP vt -> (,) <$> apa (Tr vs vq vt) vp <*> apa vP vp
eval g (e :@ b) = join (field b <$> eval g e)
eval g (r :^ q) = do
  r <- eval g r
  p <- traverse (eval g) q
  (, point1 p) <$> transport r p

idFun :: Sem TM
idFun = VL (VR E0 (Nom "") (E (V V0)))

stretch :: Sem TM -> Triple (Sem TM)
stretch vx = Tr vx (VPath (VK vx)) vx

interDeg :: INTERPOL Sem -> Int -> Bool
interDeg (INTERPOL (Pr vS vT) (Pr vf vg) (Pr vp vq) (Pr vh vk) i) = do
  pqT <- piTy "s" vS $ \ vs -> pure (VConn vs (stretch vS) vs)
  pqF <- lam pqT "s" $ \ vs -> pure (VPath (VK vs))
  hkT <- piTy "s" vS $ \ vs -> pure (VConn (VPath (VK vs))
                                           (stretch (VConn vs (stretch vS) vs))
                                           (VPath (VK vs)))
  hkF <- lam hkT "s" $ \ vs -> pure (VPath (VK (VPath (VK vs))))
  bs <- sequenceA
    [ equal VType vS vT
    , equal (vS ->> vS) vf idFun , equal (vS ->> vS) vg idFun
    , equal pqT vp pqF           , equal pqT vq pqF
    , equal hkT vh hkF           , equal hkT vk hkF
    ]
  pure $ all id bs
  
inter :: INTERPOL Sem -> Int -> Sem TM
inter i@(INTERPOL st _ _ _ (VI b)) = pure $ thing b st
inter i = do
  b <- interDeg i
  pure $ if b then thing0 (types i) else VInter i

(->>) :: Sem TM -> Sem TM -> Sem TM
vS ->> vT = VB Pi vS (VK vT)

interV :: Bit {- B0 from point j to 0 (i.e., S); B1 from 0 to point j -} ->
          INTERPOL Sem -> Sem TM -> Int -> Sem TM
interV du i@(INTERPOL st@(Pr vS vT) fg@(Pr vf vg) pq hk j) v = do
  b <- interDeg i
  if b then pure v else case (du, j) of
    (_,  VI B0)  -> pure v   -- we're already at S; up and down are both trivial
    (B0, VI B1)  -> fst <$> apf (vg, vT ->> vS) v
    (B1, VI B1)  -> fst <$> apf (vf, vS ->> vT) v
    _            -> pure (N (VInterV du i v))

keval :: Env g -> KAN (Syn g) -> Int -> KAN Sem
keval g (KAN s0 s1 b v h) =
  KAN <$> traverse (eval g) s0 <*> traverse (eval g) s1 <*> eval g b
      <*> eval g v <*> eval g h

ieval :: Env g -> INTERPOL (Syn g) -> Int -> INTERPOL Sem
ieval g (INTERPOL st fg pq hk i) =
  INTERPOL <$> traverse (eval g) st <*> traverse (eval g) fg
           <*> traverse (eval g) pq <*> traverse (eval g) hk
           <*> eval g i

piTy :: String -> Sem TM -> (Sem TM -> Int -> Sem TM) -> Int -> Sem TM
piTy n vS f = underEL vS $ \ x -> do
  let vx = N (X x)
  vT <- f vx
  tT <- quote (Q0 :\\ x) VType vT
  VB Pi vS <$> clo E0 (bnd n tT)

lam :: Sem TM -> String -> (Sem TM -> Int -> Sem TM) -> Int -> Sem TM
lam (VB Pi vS cT) n f = underEL vS $ \ x -> do
  let vx = N (X x)
  vt <- f vx
  vT <- stan cT (vx, vS)
  t <- quote (Q0 :\\ x) vT vt
  VL <$> clo E0 (bnd n t)

path :: String -> (Sem PT -> Int -> Sem TM) -> Int -> Sem TM
path x p = underPT $ \ i -> do
  vT <- p (dim i)
  tT <- quote (Q0 :\\ i) VType vT
  VPath <$> clo E0 (bnd x tT)

vpath :: Triple (Sem TM) -> String -> (Sem PT -> Int -> Sem TM) -> Int -> Sem TM
vpath vQ x p = underPT $ \ i -> do
  vT <- apa vQ (dim i)
  vt <- p (dim i)
  t  <- quote (Q0 :\\ i) vT vt
  VPath <$> clo E0 (bnd x t)

segment :: Triple (Sem TM) -> Sem PT -> Sem PT -> Int -> Triple (Sem TM)
segment p i j = Tr <$> apa p i <*> path "k" (\ k -> apa p (mux k i j)) <*> apa p j

synpa :: Syn (C0 :\ PT) TM -> Int -> Sem TM
synpa b = eval E0 (Path (bnd "i" b))

transport :: Val TM -> Triple (Sem TM) -> Int -> Sem TM
transport vr (Tr _ (VPath (VK _)) _) = pure vr  -- *obviously* degenerate
transport vr p = underPT $ \ h -> do
  vZ <- apa p (dim h)
  zZ <- quote (Q0 :\\ h) VType vZ  -- obtain syntax of typical point
  case dep (R (Nom "i") zZ) of
    Left _  -> pure vr -- *detectably* degenerate
    Right _ -> case (point0 p, zZ, point1 p) of
      (vR@(VB Sg vS0 cT0), B Sg sS tT, VB Sg vS1 cT1) -> do
        pS <- Tr vS0 <$> synpa sS <*> pure vS1
        (vs0, _) <- field B0 (vr, vR)
        let vs i = transport vs0 =<< segment pS (VI B0) i
            vT i = do
              cT <- clo (E0 :< i) tT
              stan cT =<< ((,) <$> vs i <*> apa pS i)
        (vt0, vT0) <- field B1 (vr, vR)
        (::&) <$> vs (VI B1)
              <*> (transport vt0 =<< (Tr vT0 <$> path "i" vT <*> vT (VI B1)))
      (vR@(VB Pi vS0 cT0), B Pi sS tT, vU@(VB Pi vS1 cT1)) ->
        lam vU (nomC cT1) $ \ vs1 -> do
          pS <- Tr vS0 <$> synpa sS <*> pure vS1
          let vs i = transport vs1 =<< segment pS (VI B1) i
              vT i = do
                cT <- clo (E0 :< i) tT
                stan cT =<< ((,) <$> vs i <*> apa pS i)
          (vt0, vT0) <- apf (vr, vR) =<< vs (VI B0)
          transport vt0 =<< (Tr vT0 <$> path "i" vT <*> vT (VI B1))
      (vS0 ::-: vT0, sS :-: tT, vS1 ::-: vT1) -> path "j" $ \ j -> do
        vS <- synpa sS
        vT <- synpa tT
        kan (KAN { side0 = Tr vS0 vS vS1
                 , base  = vr
                 , side1 = Tr vT0 vT vT1
                 , vert  = VI B1
                 , horiz = j})
      (VConn vs0 vQ0 vt0, Conn s qQ t, VConn vs1 vQ1 vt1) -> do
        let vQ i = traverse (eval (E0 :< i)) qQ
        path "j" $ \ j -> do
          vp0 <- apa (Tr vs0 vr vt0) j
          vQj <- path "i" $ \ i -> do
            vQi <- vQ i
            apa vQi j
          transport vp0 =<< (Tr <$> apa vQ0 j <*> pure vQj <*> apa vQ1 j)
      (_, KanT k@(KAN s0 s1 b v h), _) -> do -- faces may be degenerate...
        vk0 <- keval (E0 :< VI B0) k  -- ...so find them by instantiation
        vk1 <- keval (E0 :< VI B1) k
        vs0 <- kanV B0 vk0 vr   -- down the left face...
        let pB = VPath (VR E0 (Nom "i")
                   (E ((b ::: (point0 s0 :-: point0 s1)) :. h)))
        -- ...across the base...
        vs1 <- transport vs0 =<< (Tr <$> apa (kanB vk0) (horiz vk0)
                                     <*> pure pB
                                     <*> apa (kanB vk1) (horiz vk1))
        kanV B1 vk1 vs1  -- ...and up the right face
      (_, Inter i@(INTERPOL (Pr sS _) _ _ _ _), _) -> do
        vi0 <- ieval (E0 :< VI B0) i
        vi1 <- ieval (E0 :< VI B1) i
        vs0 <- interV B0 vi0 vr  -- down from interpolant to S0
        pS <- Tr (thing0 (types vi0)) <$> synpa sS <*>
            pure (thing0 (types vi1))
        -- from S0 to S1
        vs1 <- transport vs0 pS
        interV B1 vi1 vs1  -- up from S1 to interpolant
      _ -> pure (N (vr ::^ p))

kanB :: KAN Sem -> Triple (Sem TM)
kanB (KAN (Tr vS _ _) (Tr vT _ _) b _ _) = Tr vS b vT

-- trying to ship a value from a point in a Kan square
--   (B0) down to the base
--   (B1) or up from the base
-- must do same degeneracy tests as kan, to keep sync
kanV :: Bit -> KAN Sem -> Sem TM -> Int -> Sem TM
kanV _ k v | pteq (vert k) (VI B0) = pure v   -- on the base already
kanV du k v = case horiz k of
    VI b -> transport v =<< seg du (side b k)   -- on one side or the other
    _ -> do
      b <- (&&) <$> degenerate (side0 k) <*> degenerate (side1 k)
      pure $ if b then v else N (VKanV du k v)
  where
    seg B0 s = segment s (vert k) (VI B0)
    seg B1 s = segment s (VI B0) (vert k)

degenerate :: Triple (Sem TM) -> Int -> Bool
degenerate path = underPT $ \ i -> do
  vS <- apa path (dim i)
  sS <- quote (Q0 :\\ i) VType vS
  case bnd "i" sS of
    K _   -> pure True
    R _ _ -> pure False

kan :: KAN Sem -> Int -> Sem TM
kan k | pteq (vert k) (VI B0) = apa (kanB k) (horiz k)  -- on the base?
kan k = case horiz k of
  VI b -> apa (side b k) (vert k)  -- one one side or the other
  _ -> do -- so we're in the interior...if there is an interior
    b <- (&&) <$> degenerate (side0 k) <*> degenerate (side1 k)
    if b then apa (kanB k) (horiz k) else pure $ VKanT k

field :: Bit -> Val EL -> Int -> Val EL
field B0 (s ::& _, VB Sg sS _)  = pure (s,            sS)
field B0 (N e,     VB Sg sS _)  = pure (N (e ::@ B0), sS)
field B1 (s ::& t, VB Sg sS tT) = (t,) <$> stan tT (s, sS)
field B1 (N e,     VB Sg sS tT) = (N (e ::@ B1),) <$> stan tT (N (e ::@ B0), sS)

apa :: Triple (Sem TM) -> Sem PT -> Int -> Sem TM
apa (Tr vS _ _) (VI B0)   = pure vS
apa (Tr _ _ vT) (VI B1)   = pure vT
apa (Tr _ (VPath b) _) i  = stan b i
apa (Tr _ (N f)     _) i  = pure (N (f ::. i))

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
clo g (R x b) = pure (VR g x b)
clo g (K t)   = VK <$> eval g t

mux :: Sem PT -> Sem PT -> Sem PT -> Sem PT
mux (VI B0) p0 _ = p0
mux (VI B1) _ p1 = p1
mux (VMux i q0 q1) p0 p1 = vmux i (mux q0 p0 p1) (mux q1 p0 p1)

vmux :: FV PT -> Sem PT -> Sem PT -> Sem PT
vmux i p0 p1 | pteq p0 p1 = p0
vmux i (VMux j q0 q1) p1
  | i == j  = vmux i q0 p1
  | i < j   = vmux j (vmux i q0 p1) (vmux i q1 p1)
vmux i p0 (VMux j q0 q1)
  | i == j  = vmux i p0 q1
  | i < j   = vmux j (vmux i p0 q0) (vmux i p0 q1)
vmux i p0 p1 = VMux i p0 p1

pteq :: Sem PT -> Sem PT -> Bool
pteq (VI b) (VI c) = b == c
pteq (VMux i p0 p1) (VMux j q0 q1) =
  i == j && pteq p0 q0 && pteq p1 q1
pteq _ _ = False

data QJ :: CX -> * where
  Q0 :: QJ C0
  (:\\) :: QJ g -> FV b -> QJ (g :\ b)

data (:~:) :: t -> t -> * where
  Refl :: t :~: t

fveq :: FV a -> FV b -> Maybe (a :~: b)
fveq (Dim i _) (Dim j _) | i == j = Just Refl
fveq (Par i _ _) (Par j _ _) | i == j = Just Refl
fveq _ _ = Nothing

dbFV :: QJ g -> FV b -> Maybe (Var g b)
dbFV Q0 _ = Nothing
dbFV (q :\\ x) y = case fveq x y of
  Just Refl -> pure V0
  _         -> VS <$> dbFV q y

equal :: Sem TM -> Sem TM -> Sem TM -> Int -> Bool
equal vT vt0 vt1 = do
  t0 <- quote Q0 vT vt0
  t1 <- quote Q0 vT vt1
  pure (t0 == t1)

underEL :: Sem TM -> (FV EL -> Int -> x) -> Int -> x
underEL vS k i = k (Par i vS (Nom "")) (i + 1)

underPT :: (FV PT -> Int -> x) -> Int -> x
underPT k i = k (Dim i (Nom "")) (i + 1)

quote :: QJ g -> Sem TM -> Sem TM -> Int -> Syn g TM
quote q VType VType         = pure Type
quote q VType (VB z vS cT)  = B z <$> quote q VType vS <*>
  (underEL vS $ \ x -> do
    vx <- eval E0 (P x)
    vT <- stan cT vx
    bnd (nomC cT) <$> quote (q :\\ x) VType vT)
quote q VType (vS ::-: vT) = (:-:) <$> quote q VType vS <*> quote q VType vT
quote q VType (VConn vs vP vt) =
  Conn <$> quote q (point0 vP) vs <*> quotr q vP <*> quote q (point1 vP) vt
quote q VType (VKanT k) = KanT <$> quoka q k
quote q VType (VInter i) = Inter <$> quoin q i
quote q vF@(VB Pi vS cT) vf = underEL vS $ \ x -> do
    (vt, vT) <- apf (vf, vF) (N (X x))
    let n = case vf of
              VL (VR _ y _) -> nom y
              _ -> nomC cT
    L <$> (bnd n <$> quote (q :\\ x) vT vt)
quote q vP@(VB Sg vS cT) vp = do
  (vs, vS) <- field B0 (vp, vP)
  (vt, vT) <- field B1 (vp, vP)
  (:&) <$> quote q vS vs <*> quote q vT vt
quote q (vS ::-: vT) vq = underPT $ \ i -> do
  vS <- apa (Tr vS vq vT) =<< eval E0 (P i)
  Path <$> (bnd "i" <$> quote (q :\\ i) VType vS)
quote q (VConn vs vQ vt) vq = underPT $ \ i -> do
  vi <- eval E0 (P i)
  vP <- apa vQ vi
  vp <- apa (Tr vs vq vt) vi
  Path <$> (bnd "i" <$> quote (q :\\ i) vP vp)
  
quote q _ (N e) = E <$> (fst <$> quoel q e)
quote q t _ = \ i -> error $ "YUK! " ++ display B1 q (quote q VType t i)

quoka :: QJ g -> KAN Sem -> Int -> KAN (Syn g)
quoka q (KAN s0@(Tr vS0 _ _) s1@(Tr vS1 _ _) b v h) =
  KAN <$> quotr q s0 <*> quotr q s1 <*> quote q (vS0 ::-: vS1) b
      <*> pure (quopt q v) <*> pure (quopt q h)

hConn :: Sem TM -> Sem TM -> Sem TM -> Sem TM
hConn vT vt0 vt1 = VConn vt0 (stretch vT) vt1

quoin :: QJ g -> INTERPOL Sem -> Int -> INTERPOL (Syn g)
quoin q (INTERPOL (Pr vS vT) (Pr vf vg) (Pr vp vq) (Pr vh vk) vi) = do
  let rf vs = fst <$> apf (vf, vS ->> vT) vs
      rg vt = fst <$> apf (vg, vT ->> vS) vt
  vpTy <- piTy "s" vS $ \ vs -> hConn vS <$> (rg =<< rf vs) <*> pure vs
  vqTy <- piTy "t" vT $ \ vt -> hConn vT <$> (rf =<< rg vt) <*> pure vt
  let rp vs = fst <$> apf (vp, vpTy) vs
      rq vt = fst <$> apf (vq, vqTy) vt
  vhTy <- piTy "s" vS $ \ vs ->
    hConn <$> (hConn vT <$> (rf =<< (rg =<< rf vs)) <*> rf vs)
          <*> (rq =<< rf vs)
          <*> (vpath (stretch vT) "i" $ \ i -> do
                z <- Tr <$> (rg =<< rf vs) <*> rp vs <*> pure vs
                rf =<< apa z i)
  vkTy <- piTy "st" vT $ \ vt ->
    hConn <$> (hConn vS <$> (rg =<< (rf =<< rg vt)) <*> rg vt)
          <*> (rp =<< rg vt)
          <*> (vpath (stretch vS) "i" $ \ i -> do
                z <- Tr <$> (rf =<< rg vt) <*> rq vt <*> pure vt
                rg =<< apa z i)
  INTERPOL <$> (Pr <$> quote q VType vS        <*> quote q VType vT)
           <*> (Pr <$> quote q (vS ->> vT) vf  <*> quote q (vT ->> vS) vg)
           <*> (Pr <$> quote q vpTy vp         <*> quote q vqTy vq)
           <*> (Pr <$> quote q vhTy vh         <*> quote q vkTy vk)
           <*> pure (quopt q vi)

quotr :: QJ g -> Triple (Sem TM) -> Int -> Triple (Syn g TM)
quotr q (Tr vS0 qS vS1) =
  Tr <$> quote q VType vS0 <*> quote q (vS0 ::-: vS1) qS <*> quote q VType vS1

quoel :: QJ g -> Sem EL -> Int -> (Syn g EL, Sem TM)
quoel q (X x@(Par _ vT _)) = case dbFV q x of
  Just i   -> pure (V i, vT)
  Nothing  -> pure (P x, vT)
quoel q (vf ::$ vs) = do
  (f, VB Pi vS cT) <- quoel q vf
  (,) <$> ((f :$) <$> quote q vS vs)
      <*> stan cT (vs, vS)
quoel q (vf ::. vp) = do
  (f, vF) <- quoel q vf
  case vF of
    vS ::-: vT -> pure $ (f :. quopt q vp, VType)
    VConn vs vP vt -> (f :. quopt q vp,) <$> apa vP vp
quoel q (ve ::@ b) = do
  (e, vE@(VB Sg vS cT)) <- quoel q ve
  (_, vT) <- field b (N ve, vE)
  pure (e :@ b, vT)
quoel q (vr ::^ vp) =
  (,) <$> ((:^) <$> quote q (point0 vp) vr <*> quotr q vp)
      <*> pure (point1 vp)
quoel q (VKanV du vk vv) = do
  k <- quoka q vk
  vB <- apa (kanB vk) (horiz vk)
  let (src, trg) = case du of
        B0 -> (VKanT vk, vB)  -- if we're quoting, vk is nondegenerate
        B1 -> (vB, VKanT vk)
  v <- quote q src vv
  pure (KanV du k v, trg)
quoel q (VInterV du vi vv) = do
  i <- quoin q vi
  let vS = thing0 (types vi)
      (src, trg) = case du of
        B0 -> (VInter vi, vS)
        B1 -> (vS, VInter vi)
  v <- quote q src vv
  pure (InterV du i v, trg)

quopt :: QJ g -> Sem PT -> Syn g PT
quopt q (VI b) = I b
quopt q (VMux x p0 p1) = Mux p (quopt q p0) (quopt q p1) where
  p = case dbFV q x of
        Just i   -> V i
        Nothing  -> P x

display :: Bit {- B1 is big; B0 is small -} -> QJ g -> Syn g b -> String

display z q (Mux i (I B0) (I B1)) = display z q i
display z q (Mux i (I B1) (I B0)) = "!" ++ display z q i
display z q (E e) = display z q e
display z q (V i) = display z q (P (qproj q i))

display _ q (I b) = show b
display _ q Type = "Type"
display _ q (P (Dim _ i)) = show i
display _ q (P (Par _ _ x)) = show x

display B0 q t = "(" ++ display B1 q t ++ ")"

display _ q (Mux i j k) = concat
  [display B0 q j, "<", display B1 q i, ">", display B0 q k]
display _ q (B b s (K t)) = concat
  [display B0 q s, " ", show b, " ", display B1 q t]
display _ q (B b s (R x t)) = concat
  ["(", y, " : ", display B1 q s, ") ", show b, " " ,display B1 (glomE q y) t]
  where y = freshen q (nom x)
display _ q (L (K t)) = "\\ _ -> " ++ display B1 q t
display _ q (L (R x t)) = concat ["\\ ", y, " -> ", display B1 (glomE q y) t]
  where y = freshen q (nom x)
display _ q (s :& t) = display B0 q s ++ ", " ++ display B1 q t
display _ q (s :-: t) = display B0 q s ++ " - " ++ display B0 q t
display _ q (Conn s p t) = concat
  [display B0 q s, " -{", displayT q p, "}- ", display B0 q t]
display _ q (Path (K _)) = "."
display _ q (Path (R x t)) = concat ["\\ ", y, " -> ", display B1 (glomP q y) t]
  where y = freshen q (nom x)
display _ q (KanT k) = displayK q k
display _ q (Inter i) = displayI q i
display _ q (s ::: t) = display B0 q s ++ " : " ++ display B1 q t
display _ q (f :$ s) = display B1 q f ++ " " ++ display B0 q s
display _ q (f :. s) = display B1 q f ++ " " ++ display B0 q s
display _ q (f :@ b) = display B1 q f ++ " " ++ show b
display _ q (r :^ t) = concat [display B1 q r, " {", displayT q t, "}"]
display _ q (KanV du k v) = concat
  [displayK q k, case du of {B0 -> "\\/ "; B1 -> "/\\ "}, display B1 q v]
display _ q (InterV du i v) = concat
  [displayI q i, case du of {B0 -> "\\/ "; B1 -> "/\\ "}, display B1 q v]

displayT :: QJ g -> Triple (Syn g TM) -> String
displayT q (Tr _ (Path (K t)) _) = "\\ _ -> " ++ display B1 q t
displayT q (Tr _ st _) = display B1 q st

qproj :: QJ g -> Var g b -> FV b
qproj (_ :\\ v) V0 = v
qproj (q :\\ _) (VS i) = qproj q i

displayK :: QJ g -> KAN (Syn g) -> String
displayK q (KAN s0 s1 b v h) = concat
  [ "[", displayT q s0, " | ", display B1 q b, " | ", displayT q s1, "]("
  , display B1 q v, ", ", display B1 q h, ")"]

displayP :: QJ g -> Pair (Syn g TM) -> String
displayP q (Pr a b) = display B1 q a ++ " <-> " ++ display B1 q b

displayI :: QJ g -> INTERPOL (Syn g) -> String
displayI q (INTERPOL st fg pq hk i) = concat
  [ "[", displayP q st, " | ", displayP q fg, " | ", displayP q pq
  , " | ", displayP q hk, "](" , display B1 q i, ")"]

nameUsed :: QJ g -> String -> Bool
nameUsed Q0 _ = False
nameUsed (q :\\ Par _ _ (Nom x)) y = x == y || nameUsed q y
nameUsed (q :\\ Dim _ (Nom x)) y = x == y || nameUsed q y

freshen :: QJ g -> String -> String
freshen q x = if nameUsed q x then go 0 else x where
  go i = if nameUsed q xi then go (i + 1) else xi where
    xi = x ++ show i

glomE :: QJ g -> String -> QJ (g :\ EL)
glomE q x = q :\\ Par 0 VType (Nom x)  -- yuk

glomP :: QJ g -> String -> QJ (g :\ PT)
glomP q x = q :\\ Dim 0 (Nom x)  -- yuk

data Expt
  = (String, Syn C0 TM) :/ (FV EL -> Expt)
  | Go (Syn C0 EL)

instance Show Expt where
  show e = go e 0 where
    go (Go e) i = concat
      [ "----------------------\n"
      , display B1 Q0 e
      , "\n  -->\n"
      , display B1 Q0 (t ::: tT)
      ] where
      (vt, vT) = eval E0 e i
      tT = quote Q0 VType vT i
      t  = quote Q0 vT vt i
    go ((x, s) :/ e) i = concat
      [ x, " : ", display B1 Q0 s, "\n"
      , go (e (Par i (eval E0 s i) (Nom x))) (i + 1)
      ]

expt0 :: Expt
expt0 =
  ("X", Type) :/ \ xX -> ("Y", Type) :/ \ yY ->
  ("f", B Pi (E (P xX)) (K (E (P yY)))) :/ \ f ->
  ("X'", Type) :/ \ xX' -> ("Y'", Type) :/ \ yY' ->
  ("XQ", E (P xX) :-: E (P xX')) :/ \ xXQ ->
  ("YQ", E (P yY) :-: E (P yY')) :/ \ yYQ ->
  Go
   (E (P f) :^ Tr (B Pi (E (P xX)) (K (E (P yY))))
                  (Path (R (Nom "i") (B Pi (E (P xXQ :. V V0)) (K (E (P yYQ :. V V0))))))
                  (B Pi (E (P xX')) (K (E (P yY')))))

expt1 :: Expt
expt1 =
  ("X", Type) :/ \ xX -> ("Y", Type) :/ \ yY ->
  ("XY", E (P xX) :-: E (P yY)) :/ \ qXY ->
  ("x", E (P xX)) :/ \ x ->
  Go $ Path (R (Nom "i") (E (E (P x) :^
             Tr (E (P xX))
                (Path (R (Nom "j") (E (P qXY :. Mux (V V0) (I B0) (V (VS V0))))))
                (E (P qXY :. V V0)))))
       :::
       Conn (E (P x))
            (Tr (E (P xX)) (E (P qXY)) (E (P yY)))
            (E (E (P x) :^ Tr (E (P xX)) (E (P qXY)) (E (P yY))))

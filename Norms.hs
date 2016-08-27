{-# LANGUAGE DeriveFunctor, PatternSynonyms #-}

module Norms where

data Nm
  = C (Can Nm)  -- canonical construction
  | F Nm [Nm]   -- abstraction with incomplete environment
  | Ne :! Cop   -- neutral, via compositional operator (arrow, if you like)
  deriving (Show, Eq)

infixl 4 :!

eval :: [Nm] -> Nm -> Nm
eval g (C cn)    = C (fmap (eval g) cn)
eval g (F b [])  = F b g
eval g (e :! c)  = run g e -! cop g c

data Can t
  = Set | Pi t t | Nat | Inx t :% t
  | Ze | Su t | Em | Pa t t | Va t | Ap t t | La t
  -- the following must be banished by quote
  | Kf t    -- K t is the constant function returning t
  deriving (Show, Eq, Functor)

data Inx t
  = Fin | Tm | Env t
  deriving (Show, Eq, Functor)

pattern SET     = C Set
pattern PI s t  = C (Pi s t)
pattern NAT     = C Nat
pattern FIN n   = C (Fin :% n)
pattern TM n    = C (Tm :% n)
pattern ENV t n = C (Env t :% n)
pattern SUB n m = ENV (TM m) n
pattern ZE      = C Ze
pattern SU n    = C (Su n)
pattern EM      = C Em
pattern s :& t  = C (Pa s t)
pattern VA i    = C (Va i)
pattern AP f s  = C (Ap f s)
pattern LA t    = C (La t)
pattern K t     = C (Kf t)

arr :: Nm -> Nm -> Nm
arr s t = PI s (K t)

data Cop       -- identity, thinning, substitution
  = Id
  | Ma Cop     -- could be thinning, weakening, or mapping
  | Sh Cop     -- postcomposition with SU; never at the top in a normal form
  | Sb Nm Nm   -- target scope, environment
  deriving (Show, Eq)

-- smart map absorbs identity
sMa :: Cop -> Cop
sMa Id = Id
sMa c  = Ma c

-- eval for Cop pushes structurally
cop :: [Nm] -> Cop -> Cop
cop g Id       = Id
cop g (Ma c)   = sMa (cop g c)
cop g (Sh c)   = Sh (cop g c)
cop g (Sb n s) = Sb (eval g n) (eval g s)
-- but could potentially try to turn substitutions into renamings;
-- not doing so is a potential completeness hole

-- thinning then substitution
(<?) :: Cop -> Nm -> Nm
Id   <? xz = xz
Ma c <? xz = (c <? (xz -$ Pop)) :& (xz -$ Top)
Sh c <? xz = c <? (xz -$ Pop)

-- compositional operators are ... compositional
(>->) :: Cop -> Cop -> Cop
Id      >-> d = d
c       >-> Id = c
Ma c    >-> Ma d = sMa (c >-> d)
c       >-> Sh d = Sh (c >-> d)
Sh c    >-> Ma d = Sh (c >-> d)
Sb n sg >-> d = Sb (cod n d) (sg -! sMa d) where -- we know d isn't Id
  cod n Id = n
  cod n (Ma d)   = rod n d
  cod n (Sb m _) = m
  rod n Id = n
  rod (SU n) (Ma d) = SU (rod n d)
  rod n (Sh d) = SU (rod n d)
Ma c >-> Sb n sg = Sb n (c <? sg)

-- weakening of substitutions is a mere macro
wkSub :: Nm -> Nm
wkSub sg = (sg -! Ma (Ma (Sh Id))) :& VA ZE
-- note (further down) that it preserves identity by definition
-- but must check it preserves composition

infixl 4 -$!, -!

-- here's where identity substitution precomposes
(-$!) :: Ne -> Cop -> Nm
e :$ IdSub -$! Ma (Sb _ sg) = sg
e -$! c = e :! c


-- now let's make compositional operators act
(-!) :: Nm -> Cop -> Nm

-- yer main man
(e :! c) -! d = e -$! (c >-> d)

-- some basics
t -! Id = t
i -! Sh c = SU (i -! c)

-- mapping a compositional operator over an environment
EM        -! Ma c = EM
(xz :& x) -! Ma c = (xz -! Ma c) :& (x -! c)

-- weakening a thinning on a variable
ZE   -! Ma c = ZE
SU i -! Ma c = SU (i -! c)

-- hitting a term with a thinning
VA i    -! Ma c = VA (i -! c)
AP f s  -! Ma c = AP (f -! Ma c) (s -! Ma c)
LA t    -! Ma c = LA (t -! Ma (Ma c))

-- hitting a term with a substitution
VA i     -! Sb n sg     = i -$ Get (TM n) sg
AP f s   -! c@(Sb n sg) = AP (f -! c) (s -! c)
LA t     -! Sb n sg     = LA (t -! Sb (SU n) (wkSub sg))

newtype Hide x = Hide x
instance Show (Hide x) where
  show _ = ""
instance Eq (Hide x) where
  _ == _ = True

data Ne
  = V Int               -- de Bruijn index
  | P Int (Hide Nm)     -- de Bruijn level, cacheing its type
  | Ne :$ Op Nm         -- basic elimination
  | Nm ::: Nm           -- type annotation
  deriving (Show, Eq)

infixl 4 :$

run :: [Nm] -> Ne -> Nm
run g (V i)     = g !! i
run g p@(P x s) = p :! Id
run g (e :$ o)  = run g e -$ fmap (eval g) o
run g (t ::: _) = eval g t

data Op t
  = A t        -- application
  | Top        -- top projection
  | Pop        -- top deletion
  | Get t t    -- target type, environment
  | IdSub      -- identity substitution of a given size
  deriving (Show, Eq, Functor)

infixl 4 -$

-- here's how these things actually work
(-$) :: Nm -> Op Nm -> Nm

(e :! Id) -$ o = (e :$ o) :! Id -- nothing in the way of staying stuck

-- applying functions
F b g    -$ A s = eval (s : g) b
K t      -$ A _ = t

-- projecting from environments
(tz :& t) -$ Top = t
(tz :& t) -$ Pop = tz

-- pulling mapping out through projection
(e :! Ma c) -$ Top = e :$ Top -$! Id -! c
(e :! Ma c) -$ Pop = e :$ Pop -$! Id -! Ma c

-- projection from environments
i        -$ Get t (e :! Ma c) = (i -$ Get s (e :! Id)) -! c
  where ENV s _ = syn e
ZE       -$ Get t xz = xz -$ Top
SU i     -$ Get t xz = i -$ Get t (xz -$ Pop)
(e :! c) -$ Get t xz = (e :$ Get t (c <? xz)) :! Id

-- identity substitution
ZE   -$ IdSub = EM
SU n -$ IdSub = wkSub (n -$ IdSub)  -- preserved by weakening, by definition

-- quote (root, level) turns every P that's at least the root back into a V
quote :: (Int, Int) -> Nm -> Nm -> Nm

-- quoting types
quote rl SET SET = SET
quote rl@(r, l) SET (PI s t) =
  PI (quote rl SET s)
     (F (quote (r, 1+l) SET (t -$ A (P l (Hide s) :! Id))) [])
quote rl SET NAT = NAT
quote rl SET (C (f :% n)) = C $ fmap (quote rl SET) f :% quote rl NAT n

-- quoting functions
quote rl@(r, l) (PI s t) f = F (quote (r, 1+l) (t -$ A x) (f -$ A x)) [] where
  x = P l (Hide s) :! Id

-- quoting natural numbers
quote rl NAT ZE = ZE
quote rl NAT (SU n) = C $ Su (quote rl NAT n)

-- quoting object variables
quote rl (FIN (SU n)) ZE = ZE
quote rl (FIN (SU n)) (SU i) = SU (quote rl (FIN n) i)

-- quoting object terms
quote rl (TM n) (VA i) = VA (quote rl (FIN n) i)
quote rl t@(TM _) (AP f s) = AP (quote rl t f) (quote rl t s)
quote rl (TM n) (LA t) = LA (quote rl (TM (SU n)) t)

-- quoting environments, expanding them
quote rl (ENV t ZE)     _ = EM
quote rl (ENV t (SU n)) g = 
  quote rl (ENV t n) (g -$ Pop) :& quote rl t (g -$ Top)

-- quoting the identity substitution composed (can this happen?)
quote rl (ENV t n) (e :$ IdSub :! Ma (Sb _ sg)) =
  quote rl (ENV t n) sg

-- quoting an environment, simplifying its compositional operator
quote rl (ENV t n) (e :! Ma c) = case quoneSyn rl e of
  (e, ENV s _) -> e :! sMa (go s t c) where
    go _ _ Id = Id
    go (ENV s _) (ENV t _) (Ma c) = sMa (go s t c)
    go (FIN (SU m)) (FIN (SU n)) (Ma c) = sMa (go (FIN m) (FIN n) c)
    go (TM m) (TM n) c = quosub rl m n c
    go (FIN m) (FIN (SU n)) (Sh c) = Sh (go (FIN m) (FIN n) c)

-- quoting a term, simplifying its compositional operator
quote rl (TM n) (e :! c) = case quoneSyn rl e of
  (e, TM m) -> e :! quosub rl m n c

-- quoting an unmapped thing is dull
quote rl _ (e :! Id) = quone rl e :! Id

-- this shouldn't happen for well typed things
quote rl t s = error ("QUOTE: " ++ show t ++ " :> " ++ show s)

-- quoting the terms embedded in a compositional operator
quosub :: (Int, Int) -> Nm -> Nm -> Cop -> Cop
quosub rl _ _ Id = Id
quosub rl m n (Sb _ tz)
  | eq rl NAT m n && eq rl (SUB n n) (n -$ IdSub) tz = Id
  | otherwise = Sb (quote rl NAT n) (quote rl (SUB m n) tz)
quosub rl m n (Ma c) = Ma c
quosub rl m n c =
  error ("QUOSUB: " ++ show m ++ " " ++ show n ++ " " ++ show c)

-- yer actual definitional equality
eq :: (Int, Int) -> Nm -> Nm -> Nm -> Bool
eq (_, l) ty s t = quote (l, l) ty s == quote (l, l) ty t

-- type reconstruction
syn :: Ne -> Nm
syn (P _ (Hide s)) = s
syn (e :$ o) = case (syn e, o) of
  (PI _ t,         A v)  -> t -$ A v
  (ENV t (SU n),   Top)  -> t
  (ENV t (SU n),   Pop)  -> ENV t n
  (NAT,          IdSub)  -> SUB (e :! Id) (e :! Id)
  (FIN n,     Get t vz)  -> t

-- quotation of neutrals
quone :: (Int, Int) -> Ne -> Ne
quone (r, l) (P k s)
  | k >= r = V (l - k - 1)
  | otherwise = P k s
quone rl (e :$ o) = case (quone rl e, syn e, o) of
  (e, PI s t,         A v)  -> e :$ A (quote rl s v)
  (e, ENV t (SU n),   Top)  -> e :$ Top
  (e, ENV t (SU n),   Pop)  -> e :$ Pop
  (e, NAT,          IdSub)  -> e :$ IdSub
  (e, FIN n,     Get t vz)  -> e :$ Get (quote rl SET t) (quote rl (ENV t n) vz)
  bad -> error ("QUONE: " ++ show bad)

-- quotation with type synthesis
quoneSyn :: (Int, Int) -> Ne -> (Ne, Nm)
quoneSyn rl e = (quone rl e, syn e)

-- test stuff

i <:> t = P i (Hide t) :! Id

n = 0 <:> NAT
m = 1 <:> NAT
sg = 2 <:> SUB n m
t = 3 <:> TM n
wt = t -! Ma (Sh Id)
wsg = wkSub sg
w'tsg = (t -! Sb m sg) -! Ma (Sh Id)
wtwsg = wt -! Sb (SU m) wsg

-- quote (4, 4) (TM (SU m)) w'tsg == quote (4, 4) (TM (SU m)) wtwsg

{-# LANGUAGE DataKinds, GADTs, KindSignatures, RankNTypes, TypeOperators
  , TypeFamilies, LambdaCase
  #-}

module Tm where

import Data.Kind

import Th


------------------------------------------------------------------------------
-- Sorts
------------------------------------------------------------------------------

-- constructors *make* terms of these sorts (the directions)...
data Dir = Chk | Syn

-- ...from clumps of terms of these sorts
data Sort
  = A Dir
  | One
  | Sort :*: Sort
  | B Sort

-- substitutions are iterated tuples
type Sb :: Nat -> Sort
type family Sb n where
  Sb  Z    = One
  Sb (S n) = Sb n :*: A Syn


------------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------------

data Tm :: Sort -> Nat -> Type where
  -- the specific theory is built with the constructor constructor
  (:$) :: Cr s d -> Tm s n -> Tm (A d) n
  -- we then have the general stuff of syntax
  V :: Tm (A Syn) (S Z)
  N :: Tm One Z
  P :: Tm p l -> Union l r n -> Tm q r -> Tm (p :*: q) n
  L :: Tm s (S n) -> Tm (B s) n
  K :: Tm s n -> Tm (B s) n

-- smart constructor and destructor for codeBruijn pairing
pair :: Tm p ^ n -> Tm q ^ n -> Tm (p :*: q) ^ n
pair (p :^ th) (q :^ ph) = case cop th ph of u :^ ps -> P p u q :^ ps

parts :: Tm (p :*: q) ^ n -> (Tm p ^ n, Tm q ^ n)
parts (P p u q :^ ps) = (p :^ (luth u -< ps), q :^ (ruth u -< ps))

-- and now yer actual constructors
data Cr :: Sort -> Dir -> Type where
  Atom :: String -> Cr One Chk
  Cons :: Cr (A Chk :*: A Chk) Chk
  Bind :: Cr (B (A Chk)) Chk
  Elim :: Cr (A Syn :*: A Chk) Chk
  Embd :: Cr (A Syn) Chk
  Rdcl :: Cr (A Chk :*: A Chk) Syn
  -- Meta :: Name -> Natty n -> Cr (Sb n) Chk

-- type Name = [(String, Int)]


------------------------------------------------------------------------------
-- Substitutions
------------------------------------------------------------------------------

data (/>) n m = Sb (Natty n) (Tm (Sb n) m) (Natty m)

-- identity
is :: Natty n -> n /> n
is n = Sb n (go n) n where
  go :: Natty i -> Tm (Sb i) i
  go Zy     = N
  go (Sy i) = P (go i) (NSS (allLeft i)) V

-- identity?
isEh :: n /> m -> Either (Positive n) (n == m)
isEh (Sb Zy N _) = Right Ry
isEh (Sb (Sy n) (P sg (NSS u) V) _) = case isEh (Sb n sg (weeEnd (luth u))) of
  Right Ry -> case noneRight u of Ry -> Right Ry
  Left (Positive n) -> Left (Positive (Sy n))
isEh (Sb (Sy n) _ _) = Left (Positive n)

class Subbable (p :: Nat -> Type) where
  (//) :: p n -> n /> m -> p m
  p // sg = case isEh sg of
    Right Ry -> p
    Left (Positive _) -> p +// sg
  (+//) :: p (S n) -> S n /> m -> p m

instance Subbable (Tm s) where
  (c :$ s) +// sg = c :$ (s +// sg)
  V +// Sb (Sy Zy) (P N u t) _ = case noneLeft u of Ry -> t
  P l u r +// sg = case roof sg u of
    Roof rh w ta -> P (l // rh) w (r // ta)
  L b +// Sb n ss m = L (b +// Sb (Sy n) (P ss (NSS (allLeft m)) V) (Sy m))
  K b +// sg = K (b +// sg)

-- and now, the roof lemma
data Roof :: Nat -> Nat -> Nat -> Type where
  Roof :: l /> k -> Union k q m -> r /> q -> Roof l r m

roof :: n /> m -> Union l r n -> Roof l r m
roof (Sb (Sy n) (P ss v t) m) = \case
  NSS u -> case roof (Sb n ss (weeEnd (luth v))) u of
    Roof sgl w (Sb r rs q) -> case lemNSS w v of
      LemNSS w' ru r' ->
        Roof sgl w' (Sb (Sy r) (P rs ru t) r')
  SNS u -> case roof (Sb n ss (weeEnd (luth v))) u of
    Roof (Sb l ls k) w sgr -> case lemNSS (flipU w) v of
      LemNSS w' lu l' ->
        Roof (Sb (Sy l) (P ls lu t) l') (flipU w') sgr
  SSS u -> case roof (Sb n ss (weeEnd (luth v))) u of
    Roof (Sb l ls k) w (Sb r rs q) -> case lemSSS w v of
      LemSSS l' lu w' ru r' -> 
        Roof (Sb (Sy l) (P ls lu t) l') w' (Sb (Sy r) (P rs ru t) r')
roof (Sb Zy N _) = \case
  ZZZ -> Roof (Sb Zy N Zy) ZZZ (Sb Zy N Zy)

data LemNSS ::  Nat -> Nat -> Nat -> Nat -> Nat -> Type where
  LemNSS :: Union l r' m
         -> Union r k r'
         -> Natty r'
         -> LemNSS l r n k m

lemNSS :: Union l r n -> Union n k m -> LemNSS l r n k m
lemNSS      w  (NSS u) = case lemNSS w u of
  LemNSS w' ru r' -> LemNSS (NSS w') (NSS ru) (Sy r')
lemNSS (NSS w) (SNS u) = case lemNSS w u of
  LemNSS w' ru r' -> LemNSS (NSS w') (SNS ru) (Sy r')
lemNSS (SNS w) (SNS u) = case lemNSS w u of
  LemNSS w' ru r' -> LemNSS (SNS w') ru r'
lemNSS (SSS w) (SNS u) = case lemNSS w u of
  LemNSS w' ru r' -> LemNSS (SSS w') (SNS ru) (Sy r')
lemNSS (NSS w) (SSS u) = case lemNSS w u of
  LemNSS w' ru r' -> LemNSS (NSS w') (SSS ru) (Sy r')
lemNSS (SNS w) (SSS u) = case lemNSS w u of
  LemNSS w' ru r' -> LemNSS (SSS w') (NSS ru) (Sy r')
lemNSS (SSS w) (SSS u) = case lemNSS w u of
  LemNSS w' ru r' -> LemNSS (SSS w') (SSS ru) (Sy r')
lemNSS ZZZ ZZZ = LemNSS ZZZ ZZZ Zy

data LemSSS :: Nat -> Nat -> Nat -> Nat -> Nat -> Type where
  LemSSS :: Natty l'
         -> Union l k l'
         -> Union l' r' m
         -> Union r k r'
         -> Natty r'
         -> LemSSS l r n k m

lemSSS :: Union l r n -> Union n k m -> LemSSS l r n k m
lemSSS w (NSS u) = case lemSSS w u of
  LemSSS l' lu w' ru r' -> LemSSS (Sy l') (NSS lu) (SSS w') (NSS ru) (Sy r')
lemSSS (NSS w) (SNS u) = case lemSSS w u of
  LemSSS l' lu w' ru r' -> LemSSS l' lu (NSS w') (SNS ru) (Sy r')
lemSSS (SNS w) (SNS u) = case lemSSS w u of
  LemSSS l' lu w' ru r' -> LemSSS (Sy l') (SNS lu) (SNS w') ru r'
lemSSS (SSS w) (SNS u) = case lemSSS w u of
  LemSSS l' lu w' ru r' -> LemSSS (Sy l') (SNS lu) (SSS w') (SNS ru) (Sy r')
lemSSS (NSS w) (SSS u) = case lemSSS w u of
  LemSSS l' lu w' ru r' -> LemSSS (Sy l') (NSS lu) (SSS w') (SSS ru) (Sy r')
lemSSS (SNS w) (SSS u) = case lemSSS w u of
  LemSSS l' lu w' ru r' -> LemSSS (Sy l') (SSS lu) (SSS w') (NSS ru) (Sy r')
lemSSS (SSS w) (SSS u) = case lemSSS w u of
  LemSSS l' lu w' ru r' -> LemSSS (Sy l') (SSS lu) (SSS w') (SSS ru) (Sy r')
lemSSS ZZZ ZZZ = LemSSS Zy ZZZ ZZZ ZZZ Zy


------------------------------------------------------------------------------
-- the Jacobian
------------------------------------------------------------------------------

data Hole :: Sort -> Nat -> Type where
  Hole :: Hole s n

data JTm
  :: Sort -- sort of the hole
  -> Nat  -- scope of the hole
  -> Sort -- sort of the term
  -> Nat  -- scope of the term
  -> Type
  where
  JC  :: Cr s d -> Hole s n -> JTm s n (A d) n
  JPL :: Hole p l -> Union l r n -> Tm q r -> JTm p l (p :*: q) n
  JPR :: Tm p l -> Union l r n -> Hole q r -> JTm q r (p :*: q) n
  JL  :: Hole s (S n) -> JTm s (S n) (B s) n
  JK  :: Hole s n -> JTm s n (B s) n

(*-) :: JTm hs hn ts tn -> Tm hs hn -> Tm ts tn
JC c Hole    *- t = c :$ t
JPL Hole u q *- p = P p u q
JPR p u Hole *- q = P p u q
JL Hole      *- b = L b
JK Hole      *- b = K b

data Tube
  :: Sort -- sort of the hole
  -> Nat  -- scope of the hole
  -> Sort -- sort of the term
  -> Nat  -- scope of the term
  -> Type
  where
  Stop :: Tube s n s n
  (:*>) :: JTm ms mn ts tn -> Tube hs hn ms mn -> Tube hs hn ts tn

infixr 6 :*>

(**-) :: Tube hs hn ts tn -> Tm hs hn -> Tm ts tn
Stop       **- t = t
(j :*> js) **- t = j *- (js **- t)


------------------------------------------------------------------------------
-- Terms with Metavariables
------------------------------------------------------------------------------

type Name = [(String, Int)]

data MT :: Sort -> Nat -> Type where
  G :: Tm s n -> MT s n
  U :: Tu s n -> MT s n

data Tu :: Sort -> Nat -> Type where
  (:->) :: Tube hs hn ts tn -> St hs hn -> Tu ts tn
infixr 5 :->

data St :: Sort -> Nat -> Type where
  Ju :: Tu p l -> Union l r n -> Tu q r -> St (p :*: q) n
  Me :: Name -> Natty k -> MT (Sb k) n -> St (A Syn) n
                        -- ^^ ORLY?
data TM :: Sort -> Nat -> Type where
  -- the specific theory is built with the constructor constructor
  (:$$) :: Cr s d -> MT s n -> TM (A d) n
  -- we then have the general stuff of syntax
  TV :: TM (A Syn) (S Z)
  TN :: TM One Z
  TP :: MT p l -> Union l r n -> MT q r -> TM (p :*: q) n
  TL :: MT s (S n) -> TM (B s) n
  TK :: MT s n -> TM (B s) n
  TM :: Name -> Natty k -> MT (Sb k) n -> TM (A Syn) n

tm :: MT s n -> TM s n
tm (G (c :$ t))  = c :$$ G t
tm (G V)         = TV
tm (G N)         = TN
tm (G (P p u q)) = TP (G p) u (G q)
tm (G (L b))     = TL (G b)
tm (G (K b))     = TK (G b)
tm (U (Stop :-> Ju p u q)) = TP (U p) u (U q)
tm (U (Stop :-> Me x n t)) = TM x n t
tm (U (JC c Hole :*> js :-> s))    = c :$$ U (js :-> s)
tm (U (JPL Hole u q :*> js :-> p)) = TP (U (js :-> p)) u (G q)
tm (U (JPR p u Hole :*> js :-> q)) = TP (G p) u (U (js :-> q))
tm (U (JL Hole :*> js :-> b))      = TL (U (js :-> b))
tm (U (JK Hole :*> js :-> b))      = TK (U (js :-> b))

mt :: TM s n -> MT s n
mt (c :$$ G t) = G (c :$ t)
mt (c :$$ U (js :-> s)) = U (JC c Hole :*> js :-> s)
mt TV = G V
mt TN = G N
mt (TP (G p) u (G q)) = G (P p u q)
mt (TP (U (js :-> p)) u (G q)) = U (JPL Hole u q :*> js :-> p)
mt (TP (G p) u (U (js :-> q))) = U (JPR p u Hole :*> js :-> q)
mt (TP (U p) u (U q)) = U (Stop :-> Ju p u q)
mt (TL (G b)) = G (L b)
mt (TL (U (js :-> b))) = U (JL Hole :*> js :-> b)
mt (TK (G b)) = G (K b)
mt (TK (U (js :-> b))) = U (JK Hole :*> js :-> b)
mt (TM x n t) = U (Stop :-> Me x n t)

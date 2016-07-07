{-# LANGUAGE DataKinds, GADTs, KindSignatures, EmptyDataDecls, TypeFamilies,
    PolyKinds, TypeOperators, PatternSynonyms #-}

module NormTree where

import Data.Traversable
import Data.Foldable
import Data.List

-- Natural numbers
data Nat = Z | S Nat

-- Singletons for natural numbers
data Natty :: Nat -> * where
  Zy :: Natty Z
  Sy :: Natty n -> Natty (S n)

-- Vectors
data Vec :: Nat -> * -> * where
  Nil  :: Vec Z x
  (:.) :: x -> Vec n x -> Vec (S n) x
infixr 5 :.

-- The following definition is a Haskellization of the
-- "fixpoint of normal functors"
-- from https://github.com/pigworker/MetaprogAgda/raw/master/notes.pdf
-- section 1.9

-- General Single Sorted Trees Containing x things
data NormTree (sh :: Nat -> * -> *)(x :: *) :: * where
  (:-) :: sh n x -> Vec n (NormTree sh x) -> NormTree sh x
  -- the sh parameter determines the possible shapes of nodes
  -- for each arity; we expect it to be a GADT or a data family
infix 4 :-

-- Here's how to say "the usual shapes, or some extra shapes,
--   but nobody else handles variables"
data ExpPlush (sh :: Nat -> *) :: Nat -> * -> * where
  Var :: x -> ExpPlush sh Z x
  Abs :: x -> ExpPlush sh (S Z) x
  App :: ExpPlush sh (S (S Z)) x
  Tup :: Natty n -> ExpPlush sh n x
  Plus :: sh n -> ExpPlush sh n x  -- see? no x in the shapes

-- You can say "no extra shapes"
data NoExt :: Nat -> * where

-- So, just the usual shapes, with strings for variables.
type Basic = NormTree (ExpPlush NoExt) String

-- The Church numeral for 2 looks like this.
church2 :: Basic
church2 = Abs "f" :- (Abs "x" :-
            (App :-
              (Var "f" :- Nil) :.
              (App :- (Var "f" :- Nil) :. (Var "x" :- Nil) :. Nil) :.
              Nil) :.
            Nil) :. Nil
-- That's easy to clean with pattern synonyms.

-- Generic calculation, e.g. of free variables, is cheap.
freeVars :: Eq x => NormTree (ExpPlush sh) x -> [x]
freeVars (Var x :- Nil) = [x]
freeVars (Abs x :- t :. Nil) = delete x (freeVars t)
freeVars (_ :- ts) = foldr (union . freeVars) [] ts


-- But what if we're multisorted?

-- The above notes generalize normal functors to containers (chapter 3)
--   (by the way, you can sort of do containers in Haskell
--    https://pigworker.wordpress.com/2015/06/06/hasochistic-containers-a-first-attempt/
--    but I digress)
-- then to indexed (i.e., multisorted) containers (chapter 4)
-- which are closed under fixpoints (section 4.5)

-- The theory of containers (and indexed containers) is a depth well plumbed
-- by Neil Ghani and his friends (e.g. Michael Abbott, Thorsten Altenkirch,
-- me, Peter Morris, Peter Hancock). The papers tend to be quite categorical,
-- which is tricky if you don't have the relevant Babelfish in your ear.
-- DBLP Neil Ghani and search for "container" for the back issues of the
-- series.
-- This paper http://www.cs.nott.ac.uk/~psztxa/publ/jpartial.pdf
-- is about differentiability of containers, but has some *pictures*
-- which might help make sense of the categorical mumbo jumbo.

-- It's a big brain upload, but it has that "threshold concept" aspect
-- of changing the way you perceive what is common to inductive data
-- structures, and to systems of interactive programming (which is
-- Hancock's key insight). Almost like you *can* see the wood for the trees.
-- The "Cambridge notes" I linked to, above, give a more
-- (Agda-)programming-oriented presentation.
-- Brain-mangling homework exercises are available on request.

-- My plan here is to drag the indexed container fixpoint construction back
-- to the finitary case. We get multisorted normal functors.
-- A *number* of recursive position becomes
--   a *list of sorts* of recursive (and nonrecursive) positions,

-- So...

-- Sorts are either terminal (Left) or nonterminal (Right).
type family Case (f :: x -> *) (g :: y -> *) (z :: Either x y) :: * where
  Case f g (Left x)  = f x
  Case f g (Right y) = g y

-- If we know how to build both, we can interpret a list of sorts.
data Kids (f :: x -> *)(g :: y -> *)(zs :: [Either x y]) :: * where
  KNil :: Kids f g '[]
  (:&) :: Case f g z -> Kids f g zs -> Kids f g (z ': zs)
infixr 5 :&

-- Now a shape is indexed by its own nonterminal sort and its kids' sorts.
data MutTree (sh :: y -> [Either x y] -> *)(v :: x -> *)(i :: y) where
  (:=) :: sh i zs -> Kids v (MutTree sh v) zs -> MutTree sh v i
infixr 4 :=

-- Let's go wild!
data Side = Pat | Exp
data Sort = Tm Side | Def | List Sort
-- Sorts are closed under list formation, term sorts and definition sorts.
-- Term sorts are either pattern or expression.

-- Now we say what the syntax trees are by describing the shapes for
-- each sort. We have only one nonterminal sort -- identifiers.
--
-- But, by way of going wild, I've added
--   "mode" whose job is to specify labelling disciplines
--      (and I'm not fussy what kind mode is)
--   "more" whose job is to specify syntax extensions
-- I'm choosing only to label variable references, but ymmv.
-- Crucially, this labelling and extensibility discipline has
-- nothing to do with the idea of how to make trees.
-- Helpfully, "more" also takes "Mode", so extensions are free
--   to negotiate their own relationships with labelling disciplines.
data Syntax :: (mode -> Sort -> [Either () Sort] -> *) ->
                mode -> Sort -> [Either () Sort] -> * where
  SNil   :: Syntax more mode (List s) '[]
  SCons  :: Syntax more mode (List s) '[Right s, Right (List s)]
  SVar   :: LabelVar mode -> Syntax more mode (Tm e)   '[Left '()]
  SCon   :: Syntax more mode (Tm e)   '[Left '(), Right (List (Tm e))]
  SAbs   :: Syntax more mode (Tm Exp) '[Left '(), Right (Tm Exp)]
  SApp   :: Syntax more mode (Tm Exp) '[Right (Tm Exp), Right (Tm Exp)]
  SLet   :: Syntax more mode (Tm Exp) '[Right (List Def), Right (Tm Exp)]
  SEqn   :: Syntax more mode Def
                      '[Left '(), Right (List (Tm Pat)), Right (Tm Exp)]
  SMore  :: more mode y zs -> Syntax more mode y zs

-- The empty extension.
data NoMore :: mode -> Sort -> [Either () Sort] -> * where

-- Two labelling disciplines.
data Mode = Plain | Fancy  -- actually, Mode should be extensible
type family LabelVar (m :: mode) :: * where
  LabelVar Plain = ()
  LabelVar Fancy = Int

-- We need to interpret the nonterminal sort somehow.
data N (i :: ()) = N String

-- Here's an example with expressions, patterns and definitions
church4 :: MutTree (Syntax NoMore Fancy) N (Tm Exp)
church4 =
  SLet := (SCons := (SEqn := N "church2"
                          :& (SCons := (SVar 1 := N "f" :& KNil)
                                    :& (SCons := (SVar 2 := N "x" :& KNil)
                                              :& (SNil := KNil)
                                              :& KNil)
                                    :& KNil)
                          :& (SApp := (SVar 1 := N "f" :& KNil)
                                   :& (SApp := (SVar 1 := N "f" :& KNil)
                                            :& (SVar 2 := N "x" :& KNil)
                                            :& KNil)
                                   :& KNil)
                          :& KNil)
                 :& (SNil := KNil)
                 :& KNil)
       :& (SApp := (SVar 0 := N "church2" :& KNil)
                :& (SVar 0 := N "church2" :& KNil)
                :& KNil)
       :& KNil

-- Now let me hide some cruft.

pattern PNil = SNil := KNil
pattern x :+ xs = SCons := x :& xs :& KNil
infixr 6 :+
pattern f :$ a = SApp := f :& a :& KNil
infixl 7 :$
pattern PV :: LabelVar mode -> String -> MutTree (Syntax NoMore mode) N (Tm e)
pattern PV i x = SVar i := N x :& KNil

church4' :: MutTree (Syntax NoMore Fancy) N (Tm Exp)
church4' =
  SLet := ((SEqn := N "church2"
                 :& PV 1 "f" :+ PV 2 "x" :+ PNil
                 :& PV 1 "f" :$ (PV 1 "f" :$ PV 2 "x")
                 :& KNil)
           :+ PNil)
       :& PV 0 "church2" :$ PV 0 "church2"
       :& KNil


-- Dull stuff

instance Traversable (Vec n) where
  traverse f Nil = pure Nil
  traverse f (x :. xs) = pure (:.) <*> f x <*> traverse f xs

instance Functor (Vec n) where
  fmap = fmapDefault

instance Foldable (Vec n) where
  foldMap = foldMapDefault

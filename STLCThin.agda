module STLCThin where

{- I'm going to show that well scoped well typed
   syntax is a presheaf over the semisimplicial
   category of contexts, despite the fact that
   it's painfully obvious. -}

{- I'll need simple types... -}

data Ty : Set where
  base : Ty              -- any old base type
  _>>_ : Ty -> Ty -> Ty  -- functions

{- ...and right-growing (i.e., backward) lists
   to put them in, to make contexts. -}

data Bwd (X : Set) : Set where
  []   : Bwd X
  _-,_ : Bwd X -> X -> Bwd X

{- Now the semisimplicial category. -}

data _<=_ {X : Set} : Bwd X -> Bwd X -> Set where
  _-^_ : forall {xz yz}
      ->  xz       <=  yz
      ->  forall             y
      ->  xz       <= (yz -, y)
  _-,_ : forall {xz yz}
      ->  xz       <=  yz
      ->  forall             y
      -> (xz -, y) <= (yz -, y)
  []   :     []    <=     []

{- Read right to left, this is exactly how to
   choose none, some or all of the entries in
   a context. (It's secretly a bit vector.)
   Read left to right, this is an embedding of
   a context into a larger one, preserving
   order. -}

{- Identity -}

iota : forall {X}(xz : Bwd X) -> xz <= xz
iota []        = []
iota (xz -, x) = iota xz -, x  -- CLUE!

{- Composition (diagrammatic) -}

_-<=-_ : forall {X}{xz yz zz : Bwd X} ->
  xz <= yz -> yz <= zz -> xz <= zz
th        -<=- (ph -^ y) = (th -<=- ph) -^ y
(th -^ y) -<=- (ph -, y) = (th -<=- ph) -^ y
(th -, y) -<=- (ph -, y) = (th -<=- ph) -, y  -- CLUE!
[]        -<=- []        = []

{- I omit the proofs because I'm in a hurry. -}

{- The two CLUEs show that context extension is
   on-the-nose covariantly functorial. -}

{- Now, here are well scoped well typed terms. -}

data _|-_ (Ga : Bwd Ty) : Ty -> Set where

  var : forall {T}
     -> ([] -, T) <= Ga  -- Ga on the *right* of <=
     ------------------
     -> Ga |- T
     
  app : forall {S T}
     -> Ga |- (S >> T)
     -> Ga |- S
     -----------------
     -> Ga |- T
     
  lam : forall {S T}
     -> (Ga -, S) |- T   -- context extension!
     -----------------
     -> Ga |- (S >> T)

{- The above is the fixpoint of a polynomial with

   O = Bwd Ty * Ty       -- contexts and types of terms
   ^
   | inl (Ga, T, x)      |-> Ga, T
   | inr (lam, Ga, S, T) |-> Ga, S >> T
   | inr (app, Ga, S, T) |-> Ga, T
   |
   S = ((Ga, t) : Bwd Ty * Ty) * ([] -, T) <= Ga
     + {lam, app} * Bwd Ty * Ty * Ty
   ^
   | lam, Ga, S, T       |-> inr (lam, Ga, S, T)
   | fun, Ga, S, T       |-> inr (app, Ga, S, T)
   | arg, Ga, S, T       |-> inr (app, Ga, S, T)
   |
   P = {lam, fun, arg} * Bwd Ty * Ty * Ty
   |
   | lam, Ga, S, T       |-> (Ga -, S), T
   | fun, Ga, S, T       |-> Ga, (S >> T)
   | arg, Ga, S, T       |-> Ga, S
   v
   I = Bwd Ty * Ty       -- contexts and types of subterms

-}

{- It is absolutely no surprise that I can now "thin"
   terms, embedding their context into a larger context. -}

_^_ : forall {Ga De T} -> Ga |- T -> Ga <= De -> De |- T
var x   ^ th = var (x -<=- th)
app f s ^ th = app (f ^ th) (s ^ th)
lam t   ^ th = lam (t ^ (th -, _))   -- Agda figures "_" out

{- And then I should prove that
     t ^ iota Ga = t
     t ^ (th -<=- ph) = (t ^ th) ^ ph
-}

{- Or rather, I SHOULDN'T, because it's OBVIOUS! -}

{- The point is that the definition of _|-_ is manifestly
   STRICTLY POSITIVE in Ga, seen as an object of _<=_.
   because it is used in morphisms only on the right
   (hence admitting postcomposition) and acted on only
   covariantly (hence allowing context extension under
   lam). I've already paid for my functor! -}

{- But Agda doesn't let me construct *functors*
     (Bwd Ty, <=) -> (Set, ->)/Ty
   so I'm forced to play stupid, work in
     |Bwd Ty| -> (Set, ->)/Ty
   and then work hard to "discover" the functoriality
   I already knew I wanted, in advance. -}

{- And that's why I'm thinking about how to expose
   the functoriality I'm looking for when giving the
   polynomial whose fixpoint I'm taking (which is
   what data declarations do, in effect). -}

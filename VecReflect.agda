module VecReflect where

data Nat : Set where
  ze : Nat
  su : Nat -> Nat

data Vec (X : Set) : Nat -> Set where
  [] : Vec X ze
  _,_ : {n : Nat} -> X -> Vec X n -> Vec X (su n)

-- we have some operations that we like...
-- ...and which obey some laws

-- green pure
pure : forall {n}{X} -> X -> Vec X n
pure {ze} x = []
pure {su n} x = x , pure x

-- green <*>
_<*>_ : forall {n S T} -> Vec (S -> T) n -> Vec S n -> Vec T n
[] <*> [] = []
(g , gs) <*> (s , ss) = g s , (gs <*> ss)

-- we write down a syntax of formulae built from those expressions
-- and embedded values (effectively, a type of quotations)

data VecFmla (X : Set)(n : Nat) : Set1 where

  -- embed values
  [_]   : Vec X n -> VecFmla X n

  -- quote green pure as red pure'
  pure' : X -> VecFmla X n

  -- quote green <*> as red <*>'
  _<*>'_ : forall {S} -> VecFmla (S -> X) n -> VecFmla S n ->
              VecFmla X n

-- we can easily evaluate quoted things (because we made them
-- so; unembed values; replace red by green

eval : forall {X n} -> VecFmla X n -> Vec X n
eval [ xs ] = xs
eval (pure' x) = pure x
eval (g <*>' s) = eval g <*> eval s

-- now, here's projection, about which we shall prove a fact

data Fin : Nat -> Set where
  fz : {n : Nat} -> Fin (su n)
  fs : {n : Nat} -> Fin n -> Fin (su n)

_!!_ : forall {X n} -> Vec X n -> Fin n -> X
(x , xs) !! fz = x
(x , xs) !! fs i = xs !! i

-- define *symbolic* projection

_!!'_ : forall {X n} -> VecFmla X n -> Fin n -> X
[ xs ] !!' i = xs !! i
pure' x !!' _ = x
(g <*>' s) !!' i = (g !!' i) (s !!' i)

-- here's equality

data _==_ {X : Set}(x : X) : X -> Set where
  refl : x == x

-- one lemma for each operation

pureLem : forall {X n}(x : X)(i : Fin n) -> (pure x !! i) == x
pureLem x fz = refl
pureLem x (fs i) = pureLem x i

appLem : forall {S T n}(gs : Vec (S -> T) n)(ss : Vec S n)(i : Fin n) ->
         ((gs <*> ss) !! i) == (gs !! i) (ss !! i)
appLem (g , gs) (s , ss) fz = refl
appLem (g , gs) (s , ss) (fs i) = appLem gs ss i

-- and now a "big stick" lemma, proven by induction over
-- formulae, deploying the lemmas for each quoted operation

evalLem : forall {X n}(f : VecFmla X n)(i : Fin n) ->
  (eval f !! i) == (f !!' i)
evalLem [ xs ] i = refl
evalLem (pure' x) i = pureLem x i
-- manually desugaring "rewrite", because rewrite needs a
-- universe-polymorphic equality and I can't be arsed
evalLem (g <*>' s) i with (eval g <*> eval s) !! i | appLem (eval g) (eval s) i
evalLem (g <*>' s) i | .((eval g !! i) (eval s !! i)) | refl
  with (eval g !! i) | (eval s !! i) | evalLem g i | evalLem s i
evalLem (g <*>' s) i
  | .((eval g !! i) (eval s !! i)) | refl | .(g !!' i) | .(s !!' i) | refl | refl
  = refl

-- So, if some random wee goal about projection from pure-<*>
-- combination shows up...

zipFact : forall {X Y Z n}(f : X -> Y -> Z)
  (xs : Vec X n)(ys : Vec Y n)(i : Fin n) ->
  (((pure f <*> xs) <*> ys) !! i) == f (xs !! i) (ys !! i)

...just hit it with a big stick!

zipFact f xs ys i = evalLem ((pure' f <*>' [ xs ]) <*>' [ ys ]) i

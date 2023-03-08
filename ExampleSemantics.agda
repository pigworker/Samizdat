module ExampleSemantics where


------------------------------------------------------------------------------
-- material usually found in the library, included for completeness
------------------------------------------------------------------------------

record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_ public
_*_ : Set -> Set -> Set
S * T = S >< \ _ -> T
infixr 10 _,_ _*_

data Nat : Set where
  ze : Nat
  su : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

data EmptySet : Set where
record Zero : Set where field .bad : EmptySet
record One : Set where constructor <>
data Two : Set where ff tt : Two

data _~_ {X : Set}(x : X) : X -> Set where
  r~ : x ~ x

_<ft>_ : forall {l}{P : Two -> Set l} -> P ff -> P tt -> (b : Two) -> P b
(f <ft> t) ff = f
(f <ft> t) tt = t

_+_ : Set -> Set -> Set
S + T = Two >< (S <ft> T)

Dec : Set -> Set
Dec X = (X -> Zero) + X

Eq? : Set -> Set
Eq? X = (x y : X) -> Dec (x ~ y)

twoEq? : Eq? Two
twoEq? ff ff = tt , r~
twoEq? ff tt = ff , \ ()
twoEq? tt ff = ff , \ ()
twoEq? tt tt = tt , r~

natEq? : Eq? Nat
natEq? ze ze = tt , r~
natEq? ze (su y) = ff , \ ()
natEq? (su x) ze = ff , \ ()
natEq? (su x) (su y) with natEq? x y
... | ff , z = ff , \ { r~ -> z r~ }
... | tt , r~ = tt , r~

data Star {X : Set}(R : X -> X -> Set)(x : X) : X -> Set where
  [] : Star R x x
  _,-_ : forall {y z} -> R x y -> Star R y z -> Star R x z

_++_ : forall {X : Set}{R : X -> X -> Set}{x y z : X}
    -> Star R x y -> Star R y z -> Star R x z
[] ++ rs' = rs'
(r ,- rs) ++ rs' = r ,- (rs ++ rs')

star : forall {X Y : Set}{R : X -> X -> Set}{S : Y -> Y -> Set}
  (f : X -> Y)(g : {x x' : X} -> R x x' -> S (f x) (f x'))
  -> forall {x x'} -> Star R x x' -> Star S (f x) (f x')
star f g [] = []
star f g (r ,- rs) = g r ,- star f g rs


------------------------------------------------------------------------------
-- this development
------------------------------------------------------------------------------

data Ty : Set where two nat : Ty

data Exp : Ty -> Set where
  T F : Exp two
  Ze : Exp nat
  Su : Exp nat -> Exp nat
  If : forall {t} -> Exp two -> Exp t -> Exp t -> Exp t
  Eq : forall {t} -> Exp t -> Exp t -> Exp two

data _=>_ : {t : Ty} -> Exp t -> Exp t -> Set where
  IfT    : forall {t}{x y : Exp t} -> If T x y => x
  IfF    : forall {t}{x y : Exp t} -> If F x y => y
  IfEval : forall {t p q}{x y : Exp t} -> p => q -> If p x y => If q x y
  SuEval : forall {x y} -> x => y -> Su x => Su y
  EqSame : forall {t}{x : Exp t} -> Eq x x => T
  EqS0   : forall {x} -> Eq (Su x) Ze => F
  Eq0S   : forall {x} -> Eq Ze (Su x) => F
  EqSS   : forall {x y} -> Eq (Su x) (Su y) => Eq x y
  EqTF   : Eq T F => F  -- I added this...
  EqFT   : Eq F T => F  -- ...and this
  EqL    : forall {t}{x y z : Exp t} -> x => z -> Eq x y => Eq z y
  EqR    : forall {t}{x y z : Exp t} -> y => z -> Eq x y => Eq x z

Va : Ty -> Set
Va two = Two
Va nat = Nat

vaEq? : {t : Ty} -> Eq? (Va t)
vaEq? {two} = twoEq?
vaEq? {nat} = natEq?

ev : forall {t} -> Exp t -> Va t
ev T = tt
ev F = ff
ev Ze = 0
ev (Su e) = su (ev e)
ev (If e t f) = (ev f <ft> ev t) (ev e)
ev (Eq e f) = fst (vaEq? (ev e) (ev f))

ve : forall {t} -> Va t -> Exp t
ve {two} ff = F
ve {two} tt = T
ve {nat} ze     = Ze
ve {nat} (su v) = Su (ve v)

_=>*_ = \ {t} -> Star (_=>_ {t})

ev=>* : {t : Ty}(x : Exp t) -> Star _=>_ x (ve (ev x))
ev=>* T = []
ev=>* F = []
ev=>* Ze = []
ev=>* (Su x) = star Su SuEval (ev=>* x)
ev=>* (If x y n) with ev x | ev=>* x
... | ff | p = star _ IfEval p ++ (IfF ,- ev=>* n)
... | tt | p = star _ IfEval p ++ (IfT ,- ev=>* y)
ev=>* (Eq x y) with ev x | ev=>* x | ev y | ev=>* y
... | x' | xp | y' | yp =
  star _ EqL xp ++ (star _ EqR yp ++ help _ x' y' (vaEq? x' y')) where
  help : (t : Ty)(x' y' : Va t)(z : Dec (x' ~ y'))
      -> Eq (ve x') (ve y') =>* ve (fst z)
  help t x' .x' (tt , r~) = EqSame ,- []
  help two ff ff (ff , z) with () <- z r~
  help two ff tt (ff , z) = EqFT ,- []
  help two tt ff (ff , z) = EqTF ,- []
  help two tt tt (ff , z) with () <- z r~
  help nat ze ze (ff , z) with () <- z r~
  help nat ze (su y') (ff , z) = Eq0S ,- []
  help nat (su x') ze (ff , z) = EqS0 ,- []
  help nat (su x') (su y') (ff , z) =
    EqSS ,- help nat x' y' (ff , \ {r~ -> z r~})

stepEv : forall {t : Ty}{x y : Exp t} -> x => y -> ev x ~ ev y
stepEv IfT = r~
stepEv IfF = r~
stepEv (IfEval {p = p} {q} e) with ev p | ev q | stepEv e
... | ff | .ff | r~ = r~
... | tt | .tt | r~ = r~
stepEv (SuEval {x} {y} e) with ev x | ev y | stepEv e
... | x' | .x' | r~ = r~
stepEv (EqSame {x = x}) with ev x | vaEq? (ev x) (ev x)
... | x' | ff , z with () <- z r~
... | x' | tt , z = r~
stepEv EqS0 = r~
stepEv Eq0S = r~
stepEv (EqSS {x} {y}) with ev x | ev y | natEq? (ev x) (ev y)
... | x' | y' | ff , z = r~
... | x' | .x' | tt , r~ = r~
stepEv EqTF = r~
stepEv EqFT = r~
stepEv (EqL {x = x} {z = z} e) with ev x | ev z | stepEv e
... | x' | .x' | r~ = r~
stepEv (EqR {y = y} {z} e) with ev y | ev z | stepEv e
... | y' | .y' | r~ = r~

diamond : forall {t : Ty}{s p q : Exp t} -> s => p -> s => q
       -> Exp t >< \ r -> (p =>* r) * (q =>* r)
diamond {s = s} sp sq = ve (ev s) , help sp , help sq where
  help : forall {t}{x y : Exp t} -> x => y -> y =>* ve (ev x)
  help {t}{x}{y} e with ev x | ev y | stepEv e | ev=>* y
  ... | x' | .x' | r~ | yp = yp

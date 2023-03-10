module ExampleSemantics where

{-
This construction was provoked by Larry Paulson's blogpost
  The semantics of a simple functional language
  https://lawrencecpaulson.github.io/2023/03/08/Fun_Semantics.html

I don't for one moment subscribe to the view that one *needs* dependent types
to do semantics. Moreover, I'm inclined to think that the use of dependent
types solely for logical *super*structure is a waste of dependent types, even
if not a waste of talent and electricity (to borrow John Peel's phraseology).

I though't I'd offer an Agda counterpart, by way of exploring a different
(and far from perfect) region of the design space. Agda is quite impoverished
when it comes to proof automation: even the most boring induction must tick
off all the cases explicitly, and as usual with today's intensional type
theories, judgemental equality brings arithmetic to an algebra fight. None of
these drawbacks is inherent to the approach, but rather a reflection of the
priorities of today's system designers, more focused on programming.

What you *do* get, however, is strong support for data representations which
build in cheap notions of validity intrinsically, and for relativising
expectations to known data. We'll see that here, using intrinsically well
typed expressions, and computing the appropriate notion of value for the type
at work. The latter makes it easy to construct an embedding from values back
to types which respect the reduction semantics, leading to a simplification
of the proof of the diamond property.
-}

------------------------------------------------------------------------------
-- material usually found in the library, included for completeness
------------------------------------------------------------------------------

{-
I include this material also because I can't cope with unicode, so I use my
own tools, instead of the library.
-}

{-
Dependent pairs give us existential quantification with solid witnesses.
-}
record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_ public
_*_ : Set -> Set -> Set
S * T = S >< \ _ -> T
infixr 10 _,_ _*_

{-
Natural numbers are given inductively, but the pragma lets us use decimal
notation.
-}
data Nat : Set where
  ze : Nat
  su : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

{-
The following constructions give us *proof-irrelevant* definitions of
empty and unit types, useful for representing bit-free propositions.
-}
data EmptySet : Set where
record Zero : Set where field .bad : EmptySet
record One : Set where constructor <>

{-
Boolean values are given as data.
-}
data Two : Set where ff tt : Two

{-
This dependent conditional operator is designed to be used in a higher-order
manner: when used to prove (b : Two) -> P b, the dependent "motive", P, will
be inferred by pattern unification.
-}
_<ft>_ : forall {l}{P : Two -> Set l} -> P ff -> P tt -> (b : Two) -> P b
(f <ft> t) ff = f
(f <ft> t) tt = t

{-
E.g., here, we encode binary sums as dependent pairs over the Booleans,
choosing between S and T on the basis of whether the bit is ff or tt,
respectively. P = \ _ -> Set is inferred.
-}
_+_ : Set -> Set -> Set
S + T = Two >< (S <ft> T)

{-
The intensional equality type is certainly a wart. In this construction,
I use it only for first-order data, where it is uncontroversial.
-}
data _~_ {X : Set}(x : X) : X -> Set where
  r~ : x ~ x

{-
A set is decided if we know whether or not it is inhabited. I align the
sum so that the tag bit is ff for "uninhabited" and tt for "inhabited".
-}
Dec : Set -> Set
Dec X = (X -> Zero) + X

{-
In particular, we shall be interested in equality decisions on bits and
numbers. A set has a decidable equality if, for any two elements, we
can determine whether their equality type is inhabited. Again, note that
the decision is a dependent pair whose first component is the result of
the *Boolean* equality test.
-}
Eq? : Set -> Set
Eq? X = (x y : X) -> Dec (x ~ y)

{-
For the Booleans, we compute the usual bitwise equality, glorified with
trivial proofs and refutations.
-}
twoEq? : Eq? Two
twoEq? ff ff = tt , r~
twoEq? ff tt = ff , \ ()
twoEq? tt ff = ff , \ ()
twoEq? tt tt = tt , r~

{-
For the numbers, the only extra work is in the step case, where we use
that su respects equality to transport the equality proof in the tt case,
and that su is injective to activate the induction hypothesis for ff.
-}
natEq? : Eq? Nat
natEq?  ze     ze    = tt , r~
natEq?  ze    (su y) = ff , \ ()
natEq? (su x)  ze    = ff , \ ()
natEq? (su x) (su y) with natEq? x y
... | ff , ih = ff , \ { r~ -> ih r~ }
... | tt , r~ = tt , r~

{-
In order to manage reduction sequences, we can make use of the generic notion
of "free category" or "reflexive-transitive closure" or "Kleene star". It's a
fancy variation on lists, where instead of an element *type*, you have some
indexed notion, R, of "dominoes", which must fit together nose-to-tail to make
a sequence.
-}
data Star {X : Set}(R : X -> X -> Set)(x : X) : X -> Set where
  []   : Star R x x
  _,-_ : forall {y z} -> R x y -> Star R y z -> Star R x z

{-
The composition is a perfectly ordinary list concatenation.
-}
_++_ : forall {X : Set}{R : X -> X -> Set}{x y z : X}
    -> Star R x y -> Star R y z -> Star R x z
[]        ++ rs' = rs'
(r ,- rs) ++ rs' = r ,- (rs ++ rs')

{-
Moreover, the construction is functorial in the appropriate way. If you have
a map f on the indices and a compatible map g on the steps, then you can
transport whole sequences, using g at each step, in a way which respects f at
the endpoints.
-}
star : forall {X Y : Set}{R : X -> X -> Set}{S : Y -> Y -> Set}
  (f : X -> Y)(g : {x x' : X} -> R x x' -> S (f x) (f x'))
  -> forall {x x'} -> Star R x x' -> Star S (f x) (f x')
star f g [] = []
star f g (r ,- rs) = g r ,- star f g rs

{-
I've used the above components in many developments. They're standard kit.
Now, let us get down to business.
-}


------------------------------------------------------------------------------
-- this development
------------------------------------------------------------------------------

{-
If you remove this commentary, the remaining construction fits in 100 lines of
Agda, tedious inductions notwithstanding.
-}

{-
Our object language has a type system with two types, for numbers and bits.
Let's be explicit about that. We get to rule out ill typed junk ab initio.
-}
data Ty : Set where two nat : Ty

{-
The type of expressions is indexed over Ty. We see that the Boolean constants
yield type two, while the Ze and Su constructors operate on nat. If takes a
Boolean condition, but allows branches and results to share any one type.
Likewise Eq is available at all types, but computes a Boolean.
-}
data Exp : Ty -> Set where
  T F : Exp two
  Ze : Exp nat
  Su : Exp nat -> Exp nat
  If : forall {t} -> Exp two -> Exp t -> Exp t -> Exp t
  Eq : forall {t} -> Exp t -> Exp t -> Exp two

{-
The one-step operational semantics is readily presented as an inductive
family indexed over redex and reduct with common type. We do not *prove*
subject reduction. We merely inspect the definition to check that no
intended behaviour is missing.

I note that in Larry's blogpost, there are no rules which allow for the
computation of Boolean equality off the diagonal. I don't know whether that
was a deliberate omission, but it strikes me as odd that Eq F T should get
stuck, rather than reducing to F.
-}
data _=>_ : {t : Ty} -> Exp t -> Exp t -> Set where
  IfT    : forall {t}{x y : Exp t}               -> If T x y => x
  IfF    : forall {t}{x y : Exp t}               -> If F x y => y
  IfEval : forall {t p q}{x y : Exp t} -> p => q -> If p x y => If q x y
  SuEval : forall {x y}                -> x => y -> Su x => Su y
  EqSame : forall {t}{x : Exp t}                 -> Eq x x => T
  EqS0   : forall {x}                            -> Eq (Su x) Ze => F
  Eq0S   : forall {x}                            -> Eq Ze (Su x) => F
  EqSS   : forall {x y}                          -> Eq (Su x) (Su y) => Eq x y
  EqTF   :                                          Eq T F => F  -- mine
  EqFT   :                                          Eq F T => F  -- ditto
  EqL    : forall {t}{x y z : Exp t}   -> x => z -> Eq x y => Eq z y
  EqR    : forall {t}{x y z : Exp t}   -> y => z -> Eq x y => Eq x z

{-
Many-step reduction is the reflexive-transitive closure of one-step reduction.
-}
_=>*_ = \ {t} -> Star (_=>_ {t})

{-
Now, when it comes to an evaluation semantics, I take a different turn.
Rather than interpreting everything as numbers, coding falsity as 0 and truth
as 1, I can choose exactly the Agda type I want to represent values of
expressions in each type. I won't have to prove that Boolean expressions never
give me a wrong number: Boolean expressions give me Boolean values.
-}
Va : Ty -> Set
Va two = Two
Va nat = Nat

{-
Moreover, because I can tell the types apart, I can see exactly how to embed
the values into the expressions as constants. It's a little harder to do that
when the values are untagged numbers.
-}
ve : forall {t} -> Va t -> Exp t
ve {two} ff = F
ve {two} tt = T
ve {nat} ze     = Ze
ve {nat} (su v) = Su (ve v)

{-
As we can decide equality for Two and for Nat, we can decide equality for
values. We have to peek at the type to see which decision proceure to invoke.
-}
vaEq? : {t : Ty} -> Eq? (Va t)
vaEq? {two} = twoEq?
vaEq? {nat} = natEq?

{-
Now, we get a type-safe evaluator, one of the classic tropes of dependently
typed programming, right back to Lennart Augustsson's Cayenne paper in 1999.
The type discipline in the input is sufficient to ensure that the semantics
fits perfectly, even though there are two object-level types at work.
-}
ev : forall {t} -> Exp t -> Va t
ev T          = tt
ev F          = ff
ev Ze         = 0
ev (Su e)     = su (ev e)
ev (If e t f) = (ev f <ft> ev t) (ev e)
ev (Eq e f)   = fst (vaEq? (ev e) (ev f))

{-
Next, we should relate the evaluation semantics with the reduction rules.
In the first instance, we may prove that every expression reduces to the
constant you get when you re-embed its value. That's not true for Larry's
semantics, but only because of the missing rules for Boolean equality,
easily remedied.
-}

ev=>* : {t : Ty}(x : Exp t) -> x =>* ve (ev x)

{-
For constants, there is nothing to do.
-}
ev=>* T  = []
ev=>* F  = []
ev=>* Ze = []

{-
For Su, we lift the reduction sequence uniformly with SuEval
-}
ev=>* (Su x) = star Su SuEval (ev=>* x)

{-
For If, we first evaluate the condition (lifted with IfEval), then
we choose a branch, then we press on and evaluate that branch.
-}
ev=>* (If e t f) with ev e | ev=>* e
... | ff | p = star _ IfEval p ++ (IfF ,- ev=>* f)
... | tt | p = star _ IfEval p ++ (IfT ,- ev=>* t)
{-
There is
something subtle to this proof: the with ev e | ev=>* e abstracts the
results of   ev e    : Va two
       and   ev=>* x : x =>* ve (ev e)
        as   b       : Two
             p       : e =>* ve b
and moreover, the goal
  If e t f =>* ve ((ev f <ft> ev t) (ev e))
becomes
  If e t f =>* ve ((ev f <ft> ev t) b)
That is, "with" not only makes the values of its scrutinees available for
inspection, it also abstracts all uses of those scrutinees in the proof,
so that when we split on b, ve b computes, and so does the conditional in
the goal. For ff, we get
  p : e =>* F
  ? : If e t f =>* ve (ev f)
hence we have e reducing to F, an IfF step, then a straightforward appeal
to ev=>* f to finish the job.
-}

{-
The same trick gets us through the Eq case, at least as far as reducing the
comparands to values. From there, what happens depends on the result of the
equality test. Here, I am careful to abstract the *whole* equality decision,
from which the evaluator merely projects the Boolean component. I obtain
both the bit and its *meaning*, at once. If the bit is tt, I know the values
agree on the nose, so EqSame is enough. The ugly part is to show that when
the values differ, we most certainly compute to false.
-}
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

{-
Nearly there, let's prove that taking one reduction step preserves the
result of evaluation. This is a tedious induction, spelt out in tedious
detail.
-}
stepEv : forall {t : Ty}{x y : Exp t} -> x => y -> ev x ~ ev y

{-
The result holds trivially whenever the step reflects the evaluator exactly.
We must still say so.
-}
stepEv IfT  = r~
stepEv IfF  = r~
stepEv EqS0 = r~
stepEv Eq0S = r~
stepEv EqTF = r~
stepEv EqFT = r~

{-
The purely structural rules require appeal to the induction hypothesis.
Note the strategic use of with on "ev before" and "ev afterwards", making the
induction hypothesis an equation between *variables* on which the goal
depends.
-}
stepEv (IfEval {p = p} {q} e) with ev p | ev q | stepEv e
... | ff | .ff | r~ = r~
... | tt | .tt | r~ = r~
stepEv (SuEval {x} {y} e) with ev x | ev y | stepEv e
... | x' | .x' | r~ = r~
stepEv (EqL {x = x} {z = z} e) with ev x | ev z | stepEv e
... | x' | .x' | r~ = r~
stepEv (EqR {y = y} {z} e) with ev y | ev z | stepEv e
... | y' | .y' | r~ = r~

{-
EqSame and EqSS involve deep equality tests, so again, we use "with" to grab
the decisions projected by the evaluator.
-}
stepEv (EqSame {x = x}) with ev x | vaEq? (ev x) (ev x)
... | x' | ff , z with () <- z r~
... | x' | tt , z = r~
stepEv (EqSS {x} {y}) with ev x | ev y | natEq? (ev x) (ev y)
... | x' | y' | ff , z = r~
... | x' | .x' | tt , r~ = r~

{-
Finally, the diamond property is a simple corollary of the above, because
*everything* reduces to its value, and taking a step *preserves* that value.
-}
diamond : forall {t : Ty}{s p q : Exp t} -> s => p -> s => q
       -> Exp t >< \ r -> (p =>* r) * (q =>* r)
diamond {s = s} sp sq = ve (ev s) , help sp , help sq where
  help : forall {t}{x y : Exp t} -> x => y -> y =>* ve (ev x)
  help {t}{x}{y} e with ev x | ev y | stepEv e | ev=>* y
  ... | x' | .x' | r~ | yp = yp

{-
I'm envious of the degree of automation that Isabelle affords: the fruit of
years of hard work. I'd like to see a similar effort in automation in the
proof machinery for dependently typed programming languages. I don't think
the type technology presents a barrier to automation: if anything, the extra
hygiene offered by precise types gives a cleaner substrate on which to build
the logical layer.

I'm certainly not claiming that dependent types are *necessary*. The best I
can hope here is to have demonstrated by example that they can sometimes offer
a helpful degree of extra comfort.
-}

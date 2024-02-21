module StackM where

{-
    Types of Truth

    Conor McBride

    Mathematically Structured Programming
    Computer and Information Sciences
    University of Strathclyde
-}

{- This file is Agda code. If you load it in an Agda-enabled editor (e.g., emacs),
   Agda will colour it in for you, but not in the colours I like to use. Deep in
   the configuration menus, there's an option to use my colours. -}

{- We have data types, quite like those in Haskell, but there are no funny
   rules about capital letters. My habit is to use Big Letters for Big Things
   (like types) and small letters for small things (like values). Agda helpfully
   colours them in for us: blue for type constructors and red for value
   constructors. And we just say directly what types the things have.
   Set is the type of types (or, more particularly, the type of types which
   never talk about types, themselves). -}

{- Haskell calls this "Bool", but I like to count the things. -}
data Two : Set where ff tt : Two

{- Numbers, we must make from potatoes, but we can ask Agda to use Arabic
   notation. -}
data Nat : Set where
  ze : Nat
  su : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

{- We can define functions (they're green) in pattern matching style, with purple
   pattern variables. Agda helps us make sure we cover all the cases. The truth we
   must tell is that whenever a function gets some input, it produces some output.
   No looping. No leaving out any possible cases. -}
_+_ : Nat -> Nat -> Nat
ze   + y = y
su x + y = su (x + y)

{- But we can also make types which tell tighter truths. Here, I generalise lists
   to paths from one point to another. The points live in some type X, and the
   paths are made of segments given by a family of types, R, indexed over where
   the segment starts and ends. Note that Agda allows me fancy mixfix notation.
   When I declare something with underscores in the name, those underscores say
   where the things go. The empty path, [], ends wherever it starts.  If we have
   a segment from x to y and a path from y to z, we can use "cons" (which I write
   asymmetrically as ,-) We're enforcing that the segments of a path all join up
   properly. And note that I'm beginning to talk about types of things using
   language that sounds like stating truths. -}
data _-[_>_ {X : Set}(x : X)(R : X -> X -> Set) : X -> Set where
  [] : x -[ R > x
  _,-_ : forall {y z} -> R x y -> y -[ R > z -> x -[ R > z
infixr 10 _,-_
infix 5 _-[_>_

{- Concatenation of paths: the code looks just like concatenation of lists, but
   look at the truth the type tells! -}
_++_ : {X : Set}{R : X -> X -> Set}{x y z : X}
    -> x -[ R > y -> y -[ R > z -> x -[ R > z
[]        ++ ss = ss
(r ,- rs) ++ ss = r ,- rs ++ ss
infixr 10 _++_

{- Now, I'm going to use paths to represent programs in the machine code of a
   stack machine. The individual instructions don't make sense in all circumstances.
   We must rather care about what types of things are on the stack to ensure that a
   given instruction is appropriate. How to way say what's on the stack? With a
   stack of types! I write stacks as lists which grow on the *right*. One boring
   but vital lesson I have learned in my life is to mind the spatial properties of
   my program texts. I would rather have more types of list than flip my head. -}

{- Note that I reuse []. Agda will disambiguate. I write -, for "snoc", growing lists
   on the right. -}
data Bwd (X : Set) : Set where
  []   : Bwd X
  _-,_ : Bwd X -> X -> Bwd X
infixl 10 _-,_

{- I will have two types of stack entry: bits and numbers. -}
data Ty : Set where
  `Two : Ty
  `Nat : Ty

{- I can write a program saying which Agda types represent values in which stack
   entry types. -}
Val : Ty -> Set
Val `Two = Two
Val `Nat = Nat

{- And now I can say what the instructions are, and what stack transitions they make. -}
data Inst : Bwd Ty -> Bwd Ty -> Set where
        -- we can push a value onto the stack
  PSH : forall {Tz T} -> Val T -> Inst Tz (Tz -, T)
        -- we can add the top two numbers on the stack and put their sum back
  ADD : forall {Tz} -> Inst (Tz -, `Nat -, `Nat) (Tz -, `Nat)
        -- if there's a bit on top of the stack, we can choose between code paths
  PAF : forall {Tz Uz}(fc tc : Tz -[ Inst > Uz) -> Inst (Tz -, `Two) Uz

{- What is a stack? It's a kind of truth, that we know a value of the right type for
   every entry in the stack of types. So let's have a type for that. -}
data [Bwd] {X : Set}(P : X -> Set) : Bwd X -> Set where
  []   : [Bwd] P []
  _-,_ : forall {xz x} -> [Bwd] P xz -> P x -> [Bwd] P (xz -, x)

{- Now let's say how to run a program that gets us from one stack state to another. -}
infixl 5 _!>_
_!>_ : forall {Tz Uz} -> [Bwd] Val Tz -> Tz -[ Inst > Uz -> [Bwd] Val Uz
vz !> [] = vz
vz !> PSH x ,- is = vz -, x !> is
vz -, m -, n !> ADD ,- is = vz -, (m + n) !> is
vz -, ff !> PAF fc tc ,- is = vz !> fc !> is
vz -, tt !> PAF fc tc ,- is = vz !> tc !> is

{- Now, let's put a simple functional programming language on top. -}
data Expr : Ty -> Set where
  val : {T : Ty} -> Val T -> Expr T
  _+E_ : Expr `Nat -> Expr `Nat -> Expr `Nat
  if_then_else_ : forall {T} -> Expr `Two -> Expr T -> Expr T -> Expr T

{- We can have a reference interpreter which promises a value for every expression. -}
eval : forall {T} -> Expr T -> Val T
eval (val x) = x
eval (e +E e') = eval e + eval e'
eval (if eb then et else ef) with eval eb  -- "with" brings the value of something to the left
eval (if eb then et else ef) | ff = eval ef
eval (if eb then et else ef) | tt = eval et

{- Now, let's compile expressions. We should be able to start with any stack, and end with
   one more value on the stack than we had at the start. -}
compile : forall {Tz T} -> Expr T -> Tz -[ Inst > Tz -, T
compile (val x) = PSH x ,- []
compile (e +E e') = compile e ++ compile e' ++ ADD ,- []
compile (if e then et else ef) = compile e ++ PAF (compile ef) (compile et) ,- []


{- But we don't know our compiler gives *correct* code. Let's prove it. We will need to
   state an equation. -}

data _~_ {X : Set}(x : X) : X -> Set where
  r~ : x ~ x
infix 1 _~_

{- This is fancy notation for writing equational explanations that you can read! -}
_~[_>_ : forall {X}(x : X){y z : X} -> x ~ y -> y ~ z -> x ~ z
x ~[ r~ > q = q
_[QED] : forall {X}(x : X) -> x ~ x
x [QED] = r~
infixr 2 _~[_>_
infixr 3 _[QED]

{- Doing the same function to equal inputs gives you equal outputs. -}
_$~_ : {S T : Set}(f : S -> T){x y : S} -> x ~ y -> f x ~ f y
f $~ r~ = r~

{- We'll need to run our program a bit at a time. That means we need the fact that running
   a whole program gives the same answer as running the beginning then the end. The way you
   do a proof like this is to trick the programs involved into taking a step. -}
runs : forall {Sz Tz Uz}(vz : [Bwd] Val Sz)(is : Sz -[ Inst > Tz)(js : Tz -[ Inst > Uz)
    -> vz !> is ++ js ~ vz !> is !> js
runs vz [] js = r~
runs vz (PSH x ,- is) js = runs _ is js
runs (vz -, m -, n) (ADD ,- is) js = runs _ is js
runs (vz -, ff) (PAF fc tc ,- is) js = runs _ is js
runs (vz -, tt) (PAF fc tc ,- is) js = runs _ is js

{- Now we can prove that running compiled code for an expression effectively pushes the
   value of the expression. -}
agree : forall {Tz T}(vz : [Bwd] Val Tz)(e : Expr T)
     -> vz !> compile e ~ (vz -, eval e)
agree vz (val x) = r~
agree vz (e +E e') =
  vz !> compile (e +E e')
    ~[ r~ >
  vz !> compile e ++ compile e' ++ ADD ,- []
    ~[ runs vz (compile e) _ >
  vz !> compile e !> compile e' ++ ADD ,- []
    ~[ (_!> compile e' ++ ADD ,- []) $~ agree vz e >
  vz -, eval e !> compile e' ++ ADD ,- []
    ~[ runs (vz -, _) (compile e') _ >
  vz -, eval e !> compile e' !> ADD ,- []
    ~[ (_!> ADD ,- []) $~ agree (vz -, _) e' >
  vz -, eval e -, eval e' !> ADD ,- []
    ~[ r~ >
  (vz -, eval (e +E e'))
    [QED]
agree vz (if e then et else ef) with eval e | agree vz e  -- double with!
agree vz (if e then et else ef) | ff | bq = 
  vz !> compile e ++ PAF (compile ef) (compile et) ,- []
    ~[ runs vz (compile e) _ >
  vz !> compile e !> PAF (compile ef) (compile et) ,- []
    ~[ (_!> PAF (compile ef) (compile et) ,- []) $~ bq >
  vz -, ff !> PAF (compile ef) (compile et) ,- []
    ~[ agree vz ef >
  vz -, eval ef
    [QED]
agree vz (if e then et else ef) | tt | bq =
  vz !> compile e ++ PAF (compile ef) (compile et) ,- []
    ~[ runs vz (compile e) _ >
  vz !> compile e !> PAF (compile ef) (compile et) ,- []
    ~[ (_!> PAF (compile ef) (compile et) ,- []) $~ bq >
  vz -, tt !> PAF (compile ef) (compile et) ,- []
    ~[ agree vz et >
  vz -, eval et
    [QED]


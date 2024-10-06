module TakeOdd where

-- here be lists
data List (X : Set) : Set where
  []   : List X
  _,-_ : X -> List X -> List X
infixr 10 _,-_

-- and here be their large eliminator
elimList : forall {l X}(xs : List X)(P : List X -> Set l)
  -> P []
  -> (forall x xs -> P xs -> P (x ,- xs))
  -> P xs
elimList    []     P n c = n
elimList (x ,- xs) P n c = c x xs (elimList xs P n c)

-- no more pattern matching on lists!

-- derive case analysis
caseList : forall {l X}(xs : List X)(P : List X -> Set l)
  -> P []
  -> (forall x xs -> P (x ,- xs))
  -> P xs
caseList xs P n c = elimList xs P n (\ x xs pxs -> c x xs)

-- to define the recursor, let's have tuple kit
record One {l} : Set l where
  constructor <>

record _><_ {l}(S : Set l)(T : S -> Set l) : Set l where
  constructor _,_
  no-eta-equality
  field
    fst : S
    snd : T fst
open _><_ public
_*_ : forall {l} -> Set l -> Set l -> Set l
S * T = S >< \ _ -> T

-- now define the memo structure for lists
BelowList : forall {l X} -> (List X -> Set l) -> (List X -> Set l)
BelowList P xs = elimList xs (\ _ -> Set _) One (\ x xs H -> P xs * H)

-- show that it's constructoable
belowList : forall {l X}(xs : List X)(P : List X -> Set l)
  -> ((xs : List X) -> BelowList P xs -> P xs)
  -> BelowList P xs
belowList xs P m = elimList xs (BelowList P) <> (\ x xs bPxs -> m xs bPxs , bPxs)

-- and now we get the recursor
recList : forall {l X}(xs : List X)(P : List X -> Set l)
  -> ((xs : List X) -> BelowList P xs -> P xs)
  -> P xs
recList xs P m = m xs (belowList xs P m)

-- the relational story
data [TakeOdd_]~_ {X : Set} : List X -> List X -> Set where
  takeOddNil : [TakeOdd [] ]~ []
  takeOddOne : forall x -> [TakeOdd x ,- [] ]~ []
  takeOddTwo : forall x y {zs os} -> [TakeOdd zs ]~ os -> [TakeOdd x ,- y ,- zs ]~ (y ,- os)

mkTakeOdd : {X : Set}(xs : List X) -> _ >< [TakeOdd xs ]~_
mkTakeOdd xs = recList xs (\ xs -> _ >< [TakeOdd xs ]~_)
  \ xs -> caseList xs
    (\ xs ->  BelowList (\ xs -> _ >< [TakeOdd xs ]~_) xs -> _ >< [TakeOdd xs ]~_)
    (\ _ -> _ , takeOddNil)
    \ x ys -> caseList ys
      (\ ys -> BelowList (\ xs -> _ >< [TakeOdd xs ]~_) (x ,- ys)
            -> _ >< [TakeOdd x ,- ys ]~_)
      (\ _ -> _ , takeOddOne x)
      \ y zs m -> _ , takeOddTwo x y (snd (fst (snd m)))

takeOdd : {X : Set} -> List X -> List X
takeOdd xs = fst (mkTakeOdd xs)

-- let's check
data _~_ {X : Set}(x : X) : X -> Set where
  r~ : x ~ x
infix 2 _~_

eqnNil : forall {X} -> takeOdd {X} [] ~ []
eqnNil = r~

eqnOne : forall {X}{x : X} -> takeOdd (x ,- []) ~ []
eqnOne = r~

eqnTwo : forall {X}{x y : X}{zs : List X} -> takeOdd (x ,- y ,- zs) ~ y ,- takeOdd zs
eqnTwo = r~

module C2W where

data Nat : Set where
  ze : Nat
  su : Nat -> Nat

data _<=_ : Nat -> Nat -> Set where
  `0_ : forall {n m} -> n <= m ->    n <= su m
  `1_ : forall {n m} -> n <= m -> su n <= su m
  [] : ze <= ze

infixr 20 `0_ `1_

infix 10 _/x\_
data _/x\_ : forall {l n m} ->
             l <= m -> n <= m -> Set where
  [] : [] /x\ []
  rr_ : forall {l n m}{th : l <= m}{ph : n <= m}
     -> th /x\ ph -> `0 th /x\ `1 ph
  ll_ : forall {l n m}{th : l <= m}{ph : n <= m}
     -> th /x\ ph -> `1 th /x\ `0 ph

data Vec (X : Set) : Nat -> Set where
  [] : Vec X ze
  _,-_ : forall {n} -> X -> Vec X n -> Vec X (su n)
infixr 20 _,-_

vec : forall {S T n} -> (S -> T)
   -> Vec S n -> Vec T n
vec f    []     =     []
vec f (s ,- ss) = f s ,- vec f ss

riffle : forall {X l n m}{th : l <= m}{ph : n <= m}
      -> Vec X l -> th /x\ ph -> Vec X n
      -> Vec X m
riffle ls [] rs = []
riffle ls (rr p) (x ,- rs) = x ,- riffle ls p rs
riffle (x ,- ls) (ll p) rs = x ,- riffle ls p rs

data Two : Set where
  ff tt : Two

record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst

data Riffled {T : Two -> Set}{m : Nat}
   : Vec (Two >< T) m -> Set where
  riffling :
       forall {l}{n}{th : l <= m}{ph : n <= m}
         (ffs : Vec (T ff) l)
         (p : th /x\ ph)
         (tts : Vec (T tt) n)
         -> Riffled (riffle (vec (ff ,_) ffs)
                            p
                            (vec (tt ,_) tts))

riffled : forall (T : Two -> Set){m : Nat}
          (bts : Vec (Two >< T) m)
       -> Riffled bts
riffled T [] = riffling [] [] []
riffled T ((b , t) ,- bts) with riffled T bts
riffled T ((ff , f) ,- .(riffle (vec (ff ,_) ffs) p (vec (tt ,_) tts))) | riffling ffs p tts =
  riffling (f ,- ffs ) (ll p) tts
riffled T ((tt , t) ,- .(riffle (vec (ff ,_) ffs) p (vec (tt ,_) tts))) | riffling ffs p tts =
  riffling ffs (rr p) (t ,- tts)

data _~_ {X : Set}(x : X) : X -> Set where
  r~ : x ~ x

{-# BUILTIN EQUALITY _~_ #-}

riffle1 : forall (T : Two -> Set){m : Nat}
  {l}{n}{th : l <= m}{ph : n <= m}
         (ffs : Vec (T ff) l)
         (p : th /x\ ph)
         (tts : Vec (T tt) n)
  -> riffled T (riffle (vec (ff ,_) ffs) p (vec (tt ,_) tts)) ~ riffling ffs p tts
riffle1 T ffs (rr p) (t ,- tts)
  with riffled T (riffle (vec (ff ,_) ffs) p (vec (tt ,_) tts))
     | riffle1 T ffs p tts
... | z | w rewrite w = r~
riffle1 T (f ,- ffs) (ll p) tts
  with riffled T (riffle (vec (ff ,_) ffs) p (vec (tt ,_) tts))
     | riffle1 T ffs p tts
... | z | w rewrite w = r~
riffle1 T [] [] [] = r~

module EGTBS where

data _==_ {l}{X : Set l}(x : X) : X -> Set l where
  refl : x == x
{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}
infixl 2 _==_

data Zero : Set where

record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg
_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T
infixr 3 _,_ _*_

data Nat : Set where
  ze : Nat
  su : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

{-----------------------------------------------------------



   Everybody's Got To Be Somewhere

   Conor McBride
   Mathematically Structured Programming
   University of Strathclyde

   Trends in Functional Programming 2017















-----------------------------------------------------------}


{-----------------------------------------------------------
Warming Up

  implementing (simply typed) lambda calculus

  normalisation via hereditary substitution

  with a term representation

  explicit about relevance















-----------------------------------------------------------}

{-----------------------------------------------------------

  \x. (\y. \z. y) x

    ~~>

  \x. \z. x

(is better explored on paper)
















-----------------------------------------------------------}

{-----------------------------------------------------------
one de Bruijn thinning


    n*  i    | i < n     = i
             | otherwise = i + 1

    n* (f s) = (n* f) (n* s)

    n* (\ t) = \ (n+1)* t




(what happens if we add thinning to the syntax?)















-----------------------------------------------------------}



{----------------------------------------------------------}
-- Contexts...

data Cx (I : Set) : Set where

  []  : Cx I

  _/_ : Cx I -> I -> Cx I

infixl 4 _/_


-- the category
--
--   Thin
--
-- has contexts as objects,
--
-- but what are the morphisms?






{----------------------------------------------------------}
-- ...and Thinnings
data _<=_ {I} : Cx I -> Cx I -> Set where

  oz :                                     [] <= []

  os : forall {iz jz i} ->

                                           iz <= jz
                                  --------------------------
                                  -> (iz / i) <= (jz / i)

  o' : forall {iz jz i} ->

                                           iz <= jz
                                  --------------------------
                                  ->  iz      <= (jz / i)
infixl 3 _<=_

module Example  where
  foo : [] / 5 / 7 / 2 <= [] / 5 / 7 / 6 / 3 / 2
  foo = os (o' (o' (os (os oz))))







{----------------------------------------------------------}
-- Thinnings have identity and composition...

oi : forall {I}{iz : Cx I} ->

     iz <= iz
     
oi {_} {[]}    = oz
oi {_} {_ / _} = os oi

_-<-_ : forall {I}{iz jz kz : Cx I} ->

        jz <= kz -> iz <= jz -> iz <= kz
        
oz    -<- oz    = oz
os th -<- os ph = os (th -<- ph)
os th -<- o' ph = o' (th -<- ph)
o' th -<- ph    = o' (th -<- ph)





{----------------------------------------------------------}
-- ...which obey the usual categorical laws


oi-<- : forall {I}{iz jz : Cx I}(th : iz <= jz) ->
        oi -<- th == th
oi-<- oz = refl
oi-<- (os th) rewrite oi-<- th = refl
oi-<- (o' th) rewrite oi-<- th = refl

-<-oi : forall {I}{iz jz : Cx I}(th : iz <= jz) ->
        th -<- oi == th
-<-oi oz = refl
-<-oi (os th) rewrite -<-oi th = refl
-<-oi (o' th) rewrite -<-oi th = refl

-<-<- : forall {I}{iz jz kz lz : Cx I}
        (th : kz <= lz)(ph : jz <= kz)(ps : iz <= jz) ->
          (th -<- ph) -<- ps == th -<- (ph -<- ps)
-<-<- oz oz oz = refl
-<-<- (os th) (os ph) (os ps) rewrite -<-<- th ph ps = refl
-<-<- (os th) (os ph) (o' ps) rewrite -<-<- th ph ps = refl
-<-<- (os th) (o' ph) ps rewrite -<-<- th ph ps = refl
-<-<- (o' th) ph ps rewrite -<-<- th ph ps = refl




{----------------------------------------------------------}
-- the empty context is the initial object

on : forall {I}{iz : Cx I} -> [] <= iz
on {I} {[]}    = oz
on {I} {_ / _} = o' on


























{----------------------------------------------------------}
-- We work with thinned stuff

record _^^_ {I}(Stuff : Cx I -> Set)(scope : Cx I) : Set
 where
  constructor _^_
  field
    {support} : Cx I
    stuff     : Stuff support
    junk      : support <= scope
infixl 4 _^_

-- functoriality
_$^_ : forall {I}{S T : Cx I -> Set}
       (f : forall {iz} -> S iz -> T iz) ->
       forall {iz} -> S ^^ iz -> T ^^ iz
f $^ (s ^ th) = f s ^ th

-- thinning

_^^^_ : forall {I}{T : Cx I -> Set}{iz jz : Cx I} ->
        T ^^ iz -> iz <= jz -> T ^^ jz
(t ^ th) ^^^ ph = t ^ (ph -<- th)















{----------------------------------------------------------}
-- Relevant Data Structures

data OneR {I} : Cx I -> Set where
  <> : OneR []

void : forall {I}{iz : Cx I} -> OneR ^^ iz
void = <> ^ on




-- but what about pairing?

-- can we design          (S >< T) ^^ kz
-- packing up          (S ^^ kz) * (T ^^ kz)
-- ?

-- go back to paper and think about the slice category
--   Thin/kz









{----------------------------------------------------------}
-- the essence of coproduct diagrams

data Cop {I} : Cx I -> Cx I -> Cx I -> Set where
  czz : Cop [] [] []
  css : forall {i iz jz kz} ->
        Cop iz jz kz -> Cop (iz / i) (jz / i) (kz / i)
  cs' : forall {i iz jz kz} ->
        Cop iz jz kz -> Cop (iz / i)  jz      (kz / i)
  c's : forall {i iz jz kz} ->
        Cop iz jz kz -> Cop  iz      (jz / i) (kz / i)

lCop : forall {I}{iz jz kz : Cx I} ->
       Cop iz jz kz -> iz <= kz
lCop czz = oz
lCop (css x) = os (lCop x)
lCop (cs' x) = os (lCop x)
lCop (c's x) = o' (lCop x)

rCop : forall {I}{iz jz kz : Cx I} ->
       Cop iz jz kz -> jz <= kz
rCop czz = oz
rCop (css x) = os (rCop x)
rCop (cs' x) = o' (rCop x)
rCop (c's x) = os (rCop x)




{----------------------------------------------------------}
-- constructing coproducts

cop : forall {I}{iz             jz             kz : Cx I} ->
                (th : iz <= kz)(ph : jz <= kz) ->
      Sg (Cop iz jz ^^ kz) \ {(c ^ ps) ->
        (th == ps -<- lCop c) *
        (ph == ps -<- rCop c) }

cop  oz      oz     = czz ^ oz , refl , refl
cop (os th) (os ph) with cop th ph
cop (os .(junk -<- lCop stuff)) (os .(junk -<- rCop stuff))
  | stuff ^ junk , refl , refl
  = css stuff ^ os junk , refl , refl 
cop (os th) (o' ph) with cop th ph
cop (os .(junk -<- lCop stuff)) (o' .(junk -<- rCop stuff))
  | stuff ^ junk , refl , refl
  = cs' stuff ^ os junk , refl , refl 
cop (o' th) (os ph) with cop th ph
cop (o' .(junk -<- lCop stuff)) (os .(junk -<- rCop stuff))
  | stuff ^ junk , refl , refl
  = c's stuff ^ os junk , refl , refl  
cop (o' th) (o' ph) with cop th ph
cop (o' .(junk -<- lCop stuff)) (o' .(junk -<- rCop stuff))
  | stuff ^ junk , refl , refl
  = stuff ^ o' junk , refl , refl 






{----------------------------------------------------------}
-- relevant pairs

record _><_ {I}(S T : Cx I -> Set)(scope : Cx I) : Set where
  constructor _-[_]-_
  field
    {suppl suppr} : Cx I
    outl : S suppl
    sign : Cop suppl suppr scope
    outr : T suppr
open _><_

pair : forall {I}{S T : Cx I -> Set}{iz} ->
       S ^^ iz -> T ^^ iz -> (S >< T) ^^ iz
pair (s ^ th) (t ^ ph) with cop th ph
... | c ^ ps , p , q = (s -[ c ]- t) ^ ps





{----------------------------------------------------------}
-- variables and binding

data VarR {I}(i : I) : Cx I -> Set where
  only : VarR i ([] / i)

va : forall {I}{i : I}{iz} ->
      ([] / i) <= iz  ->  VarR i ^^ iz
va x = only ^ x

data BindR {I}(i : I)(T : Cx I -> Set)(iz : Cx I) : Set where
  ka : T iz       -> BindR i T iz
  la : T (iz / i) -> BindR i T iz

bind : forall {I}{i iz}{T : Cx I -> Set} ->
       T ^^ (iz / i) -> BindR i T ^^ iz
bind (t ^ os th) = la t ^ th
bind (t ^ o' th) = ka t ^ th





{----------------------------------------------------------}
-- simply typed lambda calculus

data Ty : Set where
  iota : Ty
  _>>_ : (S T : Ty) -> Ty

data TmR : (T : Ty)(Ga : Cx Ty) -> Set where

  var : forall {T Ga} ->
                                VarR T Ga
                            -----------------
                              -> TmR T Ga
        
  app : forall {S T Ga} ->
  
                               (TmR (S >> T) >< TmR S) Ga
                             -------------------------------
                                     -> TmR T Ga
        
  abs : forall {S T Ga} ->
  
                                   BindR S (TmR T) Ga
                               ----------------------------
                                   -> TmR (S >> T) Ga

-- every free variable has got to be somewhere!





{----------------------------------------------------------}
-- the usual de Bruijn representation

data TmI : (T : Ty)(Ga : Cx Ty) -> Set where
  var : forall {T Ga} ->
          [] / T <= Ga -> TmI T Ga
  _$_ : forall {S T Ga} ->
        TmI (S >> T) Ga -> TmI S Ga -> TmI T Ga
  lam : forall {S T Ga} ->
        TmI T (Ga / S) -> TmI (S >> T) Ga

r2i' : forall {T De Ga} -> TmR T De -> De <= Ga -> TmI T Ga
r2i' (var only) th = var th
r2i' (app (f -[ sign ]- s)) th =
  r2i' f (th -<- lCop sign) $ r2i' s (th -<- rCop sign)
r2i' (abs (ka t)) th = lam (r2i' t (o' th))
r2i' (abs (la t)) th = lam (r2i' t (os th))
r2i : forall {T Ga} -> TmR T ^^ Ga -> TmI T Ga
r2i (stuff ^ junk) = r2i' stuff junk












{----------------------------------------------------------}
-- constructing the relevant representation from de Bruijn

tmR : forall {T Ga}(t : TmI T Ga) ->
      Sg (TmR T ^^ Ga) \ t' -> t == r2i t'
tmR (var x) = var only ^ x , refl
tmR (f $ s) with tmR f | tmR s
tmR (f $ s) | f' ^ th , p | s' ^ ph , q with cop th ph
tmR (.(r2i' f' (ps -<- lCop c)) $ .(r2i' s' (ps -<- rCop c)))
  | f' ^ .(ps -<- lCop c) , refl | s' ^ .(ps -<- rCop c) , refl
  | c ^ ps , refl , refl
  = app (f' -[ c ]- s') ^ ps , refl
tmR (lam t) with tmR t
tmR (lam .(r2i' t' (os th))) | t' ^ os th , refl = abs (la t') ^ th , refl
tmR (lam .(r2i' t' (o' th))) | t' ^ o' th , refl = abs (ka t') ^ th , refl
















{----------------------------------------------------------}
-- normal forms

data Dir : Set where chk syn : Dir

data NmR : (d : Dir)(T : Ty)(Ga : Cx Ty) -> Set where

  var : forall {T Ga} ->
  
                                            VarR T Ga
                                    -----------------------
                                      -> NmR syn T Ga

  app : forall {S T Ga} ->
  
                              (NmR syn (S >> T) >< NmR chk S) Ga
                           -----------------------------------------
                                        -> NmR syn T Ga

  abs : forall {S T Ga} ->
  
                                     BindR S (NmR chk T) Ga
                                  -----------------------------
                                     -> NmR chk (S >> T) Ga

  [_] : forall {T Ga} ->

                                         NmR syn T Ga
                                     --------------------
                                       -> NmR chk T Ga

 -- fwd 2
















{----------------------------------------------------------}
data Subtract {I} (i : I) : Cx I -> Cx I -> Set where
  sz : forall {iz} -> Subtract i (iz / i) iz
  ss : forall {iz jz j} -> Subtract i iz jz -> Subtract i (iz / j) (jz / j)

data Seek {I}(i : I)(iz jz kz lz : Cx I) : Set where
  findlr : (Subtract i iz >< Subtract i jz) lz -> Seek i iz jz kz lz
  findl  : (Subtract i iz >< _==_ jz)       lz -> Seek i iz jz kz lz
  findr  : (_==_ iz       >< Subtract i jz) lz -> Seek i iz jz kz lz

seek : forall {I}{i : I}{iz jz kz lz} ->
       Subtract i kz lz -> Cop iz jz kz -> Seek i iz jz kz lz
seek sz (css c) = findlr (sz -[ c ]- sz)
seek sz (cs' c) = findl (sz -[ c ]- refl)
seek sz (c's c) = findr (refl -[ c ]- sz)
seek (ss y) (css c) with seek y c
seek (ss y) (css c) | findlr (z -[ d ]- w) = findlr (ss z -[ css d ]- ss w)
seek (ss y) (css c) | findl (z -[ d ]- refl) = findl (ss z -[ css d ]- refl)
seek (ss y) (css c) | findr (refl -[ d ]- w) = findr (refl -[ css d ]- ss w)
seek (ss y) (cs' c) with seek y c
seek (ss y) (cs' c) | findlr (z -[ d ]- w) = findlr (ss z -[ cs' d ]- w)
seek (ss y) (cs' c) | findl (z -[ d ]- refl) = findl (ss z -[ cs' d ]- refl)
seek (ss y) (cs' c) | findr (refl -[ d ]- w) = findr (refl -[ cs' d ]- w)
seek (ss y) (c's c) with seek y c
seek (ss y) (c's c) | findlr (z -[ d ]- w) = findlr (z -[ c's d ]- ss w)
seek (ss y) (c's c) | findl (z -[ d ]- refl) = findl (z -[ c's d ]- refl)
seek (ss y) (c's c) | findr (refl -[ d ]- w) = findr (refl -[ c's d ]- ss w)


{----------------------------------------------------------}
-- why does normalisation work?
-- when we replace a head variable by a function
-- we work our way along its *spine* of arguments

data Sp : (A B : Ty)(De : Cx Ty) -> Set where
  [] : forall {A}{De} -> Sp A A De
  _::_ : forall {S T B}{De} ->
           NmR chk S ^^ De -> Sp T B De -> Sp (S >> T) B De

apps : forall {B C De} -> NmR syn B ^^ De -> Sp B C De -> NmR syn C ^^ De
apps e [] = e
apps e (s :: sp) = apps (app $^ pair e s) sp


















{----------------------------------------------------------}
hsub : forall {A B Ga De} ->
       Subtract A Ga ^^ De -> NmR chk A ^^ De ->
       NmR chk B Ga -> NmR chk B ^^ De
hsubapp : forall {A B C Ga De} ->
          Subtract A Ga ^^ De -> NmR chk A ^^ De ->
          NmR syn B Ga -> Sp B C De -> NmR chk C ^^ De
happ : forall {B C De} -> NmR chk B ^^ De -> Sp B C De -> NmR chk C ^^ De

hsub y a (abs (ka t)) = abs $^ (ka $^ hsub y a t)
hsub (y ^ th) (a ^ ph) (abs (la t)) =
  abs $^ bind (hsub (ss y ^ os th) (a ^ o' ph) t)
hsub y a [ t ] = hsubapp y a t []

hsubapp (sz ^ th) a (var only) sp = happ a sp where
hsubapp (ss () ^ junk) a (var only) sp
hsubapp (y ^ th) a (app (f -[ c ]- s)) sp with seek y c
hsubapp (y ^ th) a (app (f -[ c ]- s)) sp | findlr (z -[ d ]- w)
  = hsubapp (z ^ (th -<- lCop d)) a f (hsub (w ^ (th -<- rCop d)) a s :: sp)
hsubapp (y ^ th) a (app (f -[ c ]- s)) sp | findl (z -[ d ]- refl)
  = hsubapp (z ^ (th -<- lCop d)) a f ((s ^ (th -<- rCop d)) :: sp)
hsubapp (y ^ th) a (app (f -[ c ]- s)) sp | findr (refl -[ d ]- w)
  = [_] $^ apps (f ^ (th -<- lCop d)) (hsub (w ^ (th -<- rCop d)) a s :: sp)

happ f [] = f
happ (abs (ka t) ^ th) (s :: sp) = happ (t ^ th) sp
happ (abs (la t) ^ th) (s :: sp) = happ (hsub (sz ^ th) s t) sp
happ ([ e ] ^ th) sp = [_] $^ apps (e ^ th) sp

-- lCop rCop _-<-_






{----------------------------------------------------------}
norm' : forall {Ga T} -> TmR T Ga -> NmR chk T ^^ Ga
norm' (var only) = [ var only ] ^ os oz
norm' (app (f -[ c ]- s)) =
  happ (norm' f ^^^ lCop c) ((norm' s ^^^ rCop c) :: [])
norm' (abs (ka t)) = abs $^ (ka $^ norm' t)
norm' (abs (la t)) = abs $^ bind (norm' t)

-- lCop rCop _-<-_





















{----------------------------------------------------------}
-- Have we learned anything?































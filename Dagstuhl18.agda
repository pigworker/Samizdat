module Dagstuhl18 where

open import Agda.Primitive

------------------------------------------------------------------------------
-- FUNCTIONAL PROGRAMMING
------------------------------------------------------------------------------

id : forall {l}{X : Set l} -> X -> X
id x = x

_-_ : forall {i j k}{A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k}
      (f : {a : A}(b : B a) -> C a b)
      (g : (a : A) -> B a) ->
      (a : A) -> C a (g a)
      -- "composition" is secretly the S combinator
(f - g) a = f (g a)

ko_ : forall {k l}{S : Set k}{T : Set l}(s : S)(t : T) -> S
ko_ s t = s

infixr 3 ko_

------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- LITTLE THINGS
------------------------------------------------------------------------------

data Zero : Set where

record One : Set where constructor <>

data Two : Set where tt ff : Two

data _==_ {l}{X : Set l}(x : X) : X -> Set where
  refl : x == x
{-# BUILTIN EQUALITY _==_ #-}

------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- PAIRS OF THINGS
------------------------------------------------------------------------------

record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field               fst : S ;  snd : T fst
open Sg

_*_ _+_ : Set -> Set -> Set

S * T = Sg S \ _ -> T
infixr 5 _*_ _,_

S + T = Sg Two \ { tt -> S ; ff -> T }
pattern ll_ s = tt , s ;  pattern rr_ t = ff , t
infixr 4 _+_ ;  infixr 3 ll_ rr_

-- Pi made to look like Sg
Pi : (S : Set)(T : S -> Set) -> Set
Pi S T = (s : S) -> T s

------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- MORE FUNCTIONAL PROGRAMMING
------------------------------------------------------------------------------

\\_ : forall {S : Set}{T : S -> Set}{P : Sg S T -> Set} ->
      ((s : S) -> (t : T s) -> P (s , t)) ->
      (st : Sg S T) -> P st                         -- uncurrying
(\\ f) (s , t) = f s t
infixr 3 \\_

tick_ : forall {S T : Set}{P : T -> Set} ->
      ((t : T) -> P t) ->
      (st : S * T) -> P (snd st)                    -- disCARding
tick f = \\ ko f
infixr 3 tick_

boom : forall {T : Zero -> Set}(x : Zero) -> T x    -- exploding
boom ()

------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- INDEXING THE THINGS
------------------------------------------------------------------------------

Ix : Set -> Set1
Ix I = I -> Set

_+:_ _*:_ _-:>_ : {I : Set} -> Ix I -> Ix I -> Ix I
(S +:  T) i = S i + T i
(S *:  T) i = S i * T i
(S -:> T) i = S i -> T i
infixr 3 _-:>_ ;  infixr 4 _+:_ ;  infixr 5 _*:_


[_] <_> : forall {I : Set} -> (I -> Set) -> Set

[ P ] = forall {i} -> P i        -- P holds necessarily
< P > = Sg _ \  i  -> P i        -- P holds possibly

------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- TONY HOARE
------------------------------------------------------------------------------

record Monad {I}(M : Ix I -> Ix I) : Set1 where
  field
  
    skip : forall {Q} ->                    [ Q -:> M Q ]


    _,,_ : forall {O P Q} ->                [ O -:> M P ] -> [ P -:> M Q ]
                 
                          ->                [ O           -:>        M Q ]

  _=<<_ : forall {P Q} -> [ P -:> M Q ] -> [ M P -:> M Q ]
  _=<<_ k = (id ,, k)

  _>>=_ : forall {P Q} ->   forall {i} -> M P i             -- angel's i
                       ->     (forall {j} -> P j -> M Q j)  -- devil's j
                       ->   M Q i
          
  m >>= k = k =<< m

------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- PETER HANCOCK
------------------------------------------------------------------------------

record _|>_ (I O : Set) : Set1 where
  constructor Act
  field
    Comm : Ix O
    Resp : (o : O) -> Comm o -> Set
    next : (o : O)(c : Comm o) -> Resp o c -> I
open _|>_
infixl 2 _|>_

_$_ : forall {I O} -> I |> O -> Ix I -> Ix O

(F $ Q) o =    Sg (Comm F o) \ c ->
                                     Pi (Resp F o c) \ r ->
               Q (next F o c r)

infixl 6 _$_


------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- SOME INTERACTION STRUCTURES
------------------------------------------------------------------------------

Read : Set -> One |> One
Comm (Read X) = ko One
Resp (Read X) <> <> = X
next (Read X) = _

Write : Set -> One |> One
Comm (Write X) = ko X
Resp (Write X) <> x = One
next (Write X) = _

------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- DISCRIMINATING EXCEPTIONS
------------------------------------------------------------------------------

Exn : forall {I} -> Ix I -> I |> I
Comm (Exn E) i = E i
Resp (Exn E) i e = Zero
next (Exn E) _ _ ()

-- E gives "the set of exception packets appropriate to the state"
--     and that could be empty

------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- INTERACTION STRUCTURES COMPOSE
------------------------------------------------------------------------------

Id : {I : Set} -> I |> I
Comm Id o = One
Resp Id o <> = One
next Id o <> <> = o

_&_ : forall {I J K} -> J |> I -> K |> J -> K |> I
Comm (C & D) i         = Sg (Comm C i) \ c ->
                                                  Pi (Resp C i c) \ r ->
                          Comm D (next C i c r)
Resp (C & D) i (c , k) =                         Sg (Resp C i c) \ r ->
                                                  Resp D (next C i c r) (k r)
next (C & D) i (c , k) (r , s) = next D (next C i c r) (k r) s

------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- CHOICE, SHARED STATE
------------------------------------------------------------------------------

_|+|_ : forall {I O} -> I |> O -> I |> O -> I |> O
Comm (A |+| B) = Comm A +: Comm B 
Resp (A |+| B) o (ll ac) = Resp A o ac
next (A |+| B) o (ll ac) ar = next A o ac ar
Resp (A |+| B) o (rr bc) = Resp B o bc
next (A |+| B) o (rr bc) br = next B o bc br

State : Set -> One |> One
State S = Read S |+| Write S

------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- FRAMING
------------------------------------------------------------------------------

_>|_ : forall {I} -> (I |> I) -> forall J -> (I * J |> I * J)
Comm (C >| J) (i , j) = Comm C i
Resp (C >| J) (i , j) c = Resp C i c
next (C >| J) (i , j) c r = next C i c r , j

_|<_ : forall I {J} -> (J |> J) -> (I * J |> I * J)
Comm (I |< D) (i , j) = Comm D j
Resp (I |< D) (i , j) d = Resp D j d
next (I |< D) (i , j) d r = i , next D j d r

_>|<_ : forall {I J} -> (I |> I) -> (J |> J) -> (I * J |> I * J)
C >|< D = (C >| _) |+| (_ |< D)

------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- FILE HANDLE JIGGERY POKERY (I)
------------------------------------------------------------------------------

postulate Path : Set
postulate Char : Set

data Status : Set where opened closed : Status

data FileComm (Mode : One |> One) : Status -> Set where
  fopen   : Path -> FileComm Mode closed
  fact    : Comm Mode <> -> FileComm Mode opened
  fclose  : FileComm Mode opened

-- A gives the actions available while the file is open.

------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- FILE HANDLE JIGGERY POKERY (II)
------------------------------------------------------------------------------

FH : (Mode : One |> One) -> Status |> Status

Comm (FH Mode) o = FileComm Mode o

Resp (FH Mode) .closed (fopen x)  =  Two -- did the file actually open?

next (FH Mode) .closed (fopen x)     tt  = opened
next (FH Mode) .closed (fopen x)     ff  = closed

Resp (FH Mode) .opened (fact a)   =  Resp Mode <> a
next (FH Mode) .opened (fact a)      r   = opened

Resp (FH Mode) .opened fclose     =  One
next (FH Mode) .opened fclose        r   = closed

-- consider Mode as Read or Write...

------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- FREE MONADS ON INDEXED SETS
------------------------------------------------------------------------------

data FIx {I}(F : I |> I)(Q : Ix I) : Ix I where
  return : [ Q -:> FIx F Q ]
  !_     : [ F $ FIx F Q -:> FIx F Q ]
infixr 3 !_

_=<<_ : forall {I}{F : I |> I}{P Q} ->
        [ P -:> FIx F Q ] -> [ FIx F P -:> FIx F Q ]
k =<< return p  = k p
k =<< (! c , j) = ! c , \ r -> k =<< j r

Free : forall {I}(F : I |> I) -> Monad (FIx F)
Monad.skip (Free F) = return
Monad._,,_ (Free F) = \ op pq o -> pq =<< op o

------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- HANDLING
------------------------------------------------------------------------------

handle : forall {I}(F : I |> I){X Q : Ix I} ->
         [ X -:> Q ] ->         -- how to handle return
         [ F $ Q -:> Q ] ->     -- how to handle operations
         [ FIx F X -:> Q ]      -- the handler

handle F ret op (return x) = ret x
handle F ret op (! c , k)  = op (c , \ r -> handle F ret op (k r))

------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- COMPLETELY ITERATIVE MONADS (THE COINDUCTIVE STORY)
------------------------------------------------------------------------------

record CoFIx {I}(F : I |> I)(Q : Ix I)(i : I) : Set where
  coinductive
  constructor node
  field
    force :  (Q  +:  F $ CoFIx F Q) i
open CoFIx

retCo : forall {I}{F : I |> I}{Q : Ix I} -> [ Q -:> CoFIx F Q ]
retCo q = node (ll q)
-- !!_ : forall {I}{F : I |> I}{Q : Ix I} -> [ F $ CoFIx F Q -:> CoFIx F Q ]
pattern !!_ f = node (rr f)
infixl 3 !!_

_=<<Co_ : forall {I}{F : I |> I}{P Q} ->
         [ P -:> CoFIx F Q ] -> [ CoFIx F P -:> CoFIx F Q ]
force (k =<<Co b) with force b
force (k =<<Co b) | ll q      = force (k q)
force (k =<<Co b) | rr c , j  = rr c , \ r -> k =<<Co j r

------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- FOOTLING
------------------------------------------------------------------------------

footle : forall {I}(F : I |> I){P Q : Ix I} ->
          [ P -:> Q +: F $ P ] ->
          [ P -:> CoFIx F Q ]
force (footle F d p) with d p
force (footle F d p) | ll q      = ll q
force (footle F d p) | rr c , k  = rr c , \ r -> footle F d (k r)

------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- CONTAINER DRIVERS (IN MEMORIAM MARK E SMITH)
------------------------------------------------------------------------------

Driver : forall {I J} (_~_ : I -> J -> Set) (Hi : I |> I) (Lo : J |> J) -> Set
Driver _~_ Hi Lo = forall {i j} ->

        {- Hi -}      i  ~  j ->  {- Lo -}
  Pi (Comm Hi i)    \ c ->
                            Sg (Comm Lo j)      \ c' ->
                            Pi (Resp Lo j c')   \ r' ->
  Sg (Resp Hi i c)  \ r ->
      next Hi i c r      ~      next Lo j c' r'         

------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- THE SYNC ADJUNCTION
------------------------------------------------------------------------------

module SYNC {I J} (_~_ : I -> J -> Set) where

  SgSyncR : Ix I -> Ix J          ;   PiSyncL : Ix J -> Ix I
  SgSyncR P j = < P *: (_~ j) >   ;   PiSyncL Q i = [ (i ~_) -:> Q ]

  module SYNCADJUNCTION {P : Ix I}{Q : Ix J} where

    {-     [ P -:> PiSyncL Q ]
         ===========================
           [ SgSyncR P -:> Q ]       -}

    mkSyncR-:> : [ P -:> PiSyncL Q ]  ->  [ SgSyncR P -:> Q ]
    mk-:>SyncL : [ SgSyncR P -:> Q ]  ->  [ P -:> PiSyncL Q ]
                
    mkSyncR-:> f (_ , p , s) = f p s              
    mk-:>SyncL f p s = f (_ , p , s) 

open SYNC ; open SYNCADJUNCTION

------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- HENRY FORD
------------------------------------------------------------------------------

dullOut : forall {I}{Q : Ix I} -> [ SgSyncR _==_ Q -:> Q ]
dullOut (_ , q , refl) = q

dullIn : forall {I}{Q : Ix I} -> [ Q -:> SgSyncR _==_ Q ]
dullIn q = (_ , q , refl)

------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- CONTAINER DRIVING
------------------------------------------------------------------------------

drive : forall {I J} (_~_ : I -> J -> Set)(Hi : I |> I)(Lo : J |> J)
          (D : Driver _~_ Hi Lo){Q : Ix I} ->

          [ SgSyncR _~_ (FIx Hi Q) -:> FIx Lo (SgSyncR _~_ Q) ]

drive _~_ Hi Lo D = mkSyncR-:> _~_ {Q = FIx Lo _}
  (handle Hi {Q = PiSyncL _~_ _}
    (\ { q s -> return (_ , q , s) })
    (\ { (c , k) s -> let c' , D' = D s c in ! c' , \ r' ->
                      let r , s' = D' r' in k r s' })
  )

dullDrive : forall {I}(Hi Lo : I |> I)(D : Driver _==_ Hi Lo){Q : Ix I} ->
             [ FIx Hi Q -:> FIx Lo Q ]
dullDrive Hi Lo D t =
  (return - dullOut) =<< drive _==_ Hi Lo D (dullIn t)

------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- COINDUCTIVE CONTAINER DRIVING
------------------------------------------------------------------------------

driveCo :   forall {I J} (_~_ : I -> J -> Set)(Hi : I |> I)(Lo : J |> J)
            (D : Driver _~_ Hi Lo){Q : Ix I} ->
            [ SgSyncR _~_ (CoFIx Hi Q) -:> CoFIx Lo (SgSyncR _~_ Q) ]
driveCo _~_ Hi Lo D {Q} = footle Lo {P = SgSyncR _~_ _} help where
  help : [ SgSyncR _~_ (CoFIx Hi Q) -:>
           SgSyncR _~_ Q +: Lo $ SgSyncR _~_ (CoFIx Hi Q) ]
  help (_ , t , s) with force t
  ... | (tt , q)      = tt , _ , q , s
  ... | (ff , c , k)  = ff , let c' , D' = D s c in c' , \ r' ->
                             let r , s' = D' r' in _ , k r , s'

dullDriveCo : forall {I}(Hi Lo : I |> I)(D : Driver _==_ Hi Lo){Q : Ix I} ->
             [ CoFIx Hi Q -:> CoFIx Lo Q ]
dullDriveCo Hi Lo D t =
  (retCo - dullOut) =<<Co driveCo _==_ Hi Lo D (dullIn t)

------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- "SHELL SCRIPTING"
------------------------------------------------------------------------------

Responses : forall {I}(C : I |> I) {o} -> FIx C (ko One) o -> Set
Responses C (return <>) = One
Responses C (! c , k) = Sg (Resp C _ c) \ r -> Responses C (k r)

afterward : forall {I} (C : I |> I) (o : I) (t : FIx C (ko One) o) ->
            Responses C t -> I
afterward C o (return x) <> = o
afterward C o (! c , k) (r , rs) = afterward C (next C o c r) (k r) rs

Star : forall {I} -> I |> I -> I |> I
Comm (Star C) = FIx C (ko One)
Resp (Star C) o = Responses C
next (Star C) = afterward C

------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- "BASH"
------------------------------------------------------------------------------

run : forall {I}(C : I |> I){Q : I -> Set} ->
        [ FIx (Star C) Q -:> FIx C Q ]

run C {Q} = handle (Star C) {Q} {FIx C Q}
  return
  \ {(t , k) -> help t k } 
  where
  help : forall {o}(t : FIx C (ko One) o) ->
         ((s : Responses C t) -> FIx C Q (afterward C o t s)) -> FIx C Q o
  help (return <>) k = k <>
  help (! c , j) k = ! c , \ r -> help (j r) \ rs -> k (r , rs)

------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- "CoBASH"
------------------------------------------------------------------------------

runCo : forall {I}(C : I |> I){Q : I -> Set} ->
          [ CoFIx (C & Star C) Q -:> CoFIx C Q ]

runCo C {Q} = footle C {CoFIx (C & Star C) Q}{Q} help where
  help : [ CoFIx (C & Star C) Q -:> Q +: C $ CoFIx (C & Star C) Q ]
  help t with force t
  ... | ll q            = ll q
  ... | rr (c , j) , k  = rr c , \ r -> buff (j r) \ rs -> k (r , rs) where
    buff : forall {o}(t : FIx C (ko One) o) ->
           ((s : Responses C t) -> CoFIx (C & Star C) Q (afterward C o t s)) ->
           CoFIx (C & Star C) Q o
    buff (return <>) k = k <>
    buff (! c , j)   k = !! (c , \ r -> j r) , k

------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- NORMATIVE BEHAVIOUR
------------------------------------------------------------------------------

BothClosed : Status * Status -> Set
BothClosed (closed , closed) = One
BothClosed _                 = Zero

TightInterface : (Status * Status) |> (Status * Status)
TightInterface =

       (FH (Read (Char + One))
        >|<
        FH (Write Char))
  |+|
       Exn BothClosed

pattern rd_ c = ll ll c ;  pattern wr_ c = ll rr c
pattern raise = rr <>
infixr 3 rd_ wr_

------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- ENSURING NORMATIVE BEHAVIOUR
------------------------------------------------------------------------------

LooseInterface : (Status * Status) |> (Status * Status)
LooseInterface = (FH (Read (Char + One)) >|< FH (Write Char)) |+| Exn (ko One)

loosen : forall {Q} -> [ CoFIx LooseInterface Q -:> CoFIx TightInterface Q ]
loosen = runCo _ - dullDriveCo _ _ \
  { {i = i} refl (ll c)  ->
      ((ll c) , \ r -> return <>)        , \ { (r , <>) -> r , refl }
  ; {i = opened , opened} refl raise ->
     (  (rd fclose) , \ _ ->
      ! (wr fclose) , \ _ ->
      ! raise , boom)                    , (tick tick \\ boom)
  ; {i = opened , closed} refl raise ->
     (  (rd fclose) , \ _ ->
      ! raise , boom)                    , (tick \\ boom)
  ; {i = closed , opened} refl raise ->
     (  (wr fclose) , \ _ ->
      ! raise , boom)                    , (tick \\ boom)
  ; {i = closed , closed} refl raise ->
     (raise , boom)                      , (\\ boom)
  }

------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- COPYING FILES
------------------------------------------------------------------------------

copyGo : CoFIx LooseInterface BothClosed (opened , opened)
force copyGo = rr (rd fact <>) , \
  { (ll c)  -> !! (wr fact c) , \ _ -> copyGo
  ; (rr <>) -> !! (rd fclose) , \ _ ->
               !! (wr fclose) , \ _ ->
               retCo <>
  }

cp : Path -> Path -> CoFIx TightInterface BothClosed (closed , closed)
cp src trg = loosen (
  !! (rd fopen src) , \
  { tt -> !! (wr fopen trg) , \
      { tt -> copyGo
      ; ff -> !! raise , boom
      }
  ; ff -> !! raise , boom
  } )

------------------------------------------------------------------------------

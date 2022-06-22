module SmolCat where

open import Basics

record Cat {O : Set}(A : O -> O -> Set) : Set1 where
  field
    iden : forall {o} -> A o o
    [_&_]~_ : forall {R S T} -> A R S -> A S T -> A R T -> Set
    tri  : forall {R S T}(f : A R S)(g : A S T) -> < [ f & g ]~_ >
    triq : forall {R S T}{f : A R S}{g : A S T}(v w : < [ f & g ]~_ >) -> v ~ w
    idTri : forall {S T}(f : A S T) -> [ iden & f ]~ f
    triId : forall {S T}(f : A S T) -> [ f & iden ]~ f
    ass03 : forall {X0 X1 X2 X3}
      {f01 : A X0 X1}{f02 : A X0 X2}{f23 : A X2 X3}{f13 : A X1 X3}
      -> < [ f01 &_]~ f02 *: [_& f23 ]~ f13 >
      -> < [ f01 & f13 ]~_ *: [ f02 & f23 ]~_ >
  infix 45 [_&_]~_
  ass02 : forall {X0 X1 X2 X3}
      {f01 : A X0 X1}{f03 : A X0 X3}{f12 : A X1 X2}{f23 : A X2 X3}
      -> < [ f01 &_]~ f03 *: [ f12 & f23 ]~_ >
      -> < [ f01 & f12 ]~_ *: [_& f23 ]~ f03 >
  ass02 {f01 = f01}{f03}{f12}{f23} (v013 ^ v123)
    with f02 , v012 <- tri f01 f12
       | w013 ^ v023 <- ass03 (v012 ^ v123)
       | r~ <- triq (! v013) (! w013)
       = v012 ^ v023
  ass13 : forall {X0 X1 X2 X3}
      {f01 : A X0 X1}{f03 : A X0 X3}{f12 : A X1 X2}{f23 : A X2 X3}
      -> < [ f01 & f12 ]~_ *: [_& f23 ]~ f03 >
      -> < [ f01 &_]~ f03 *: [ f12 & f23 ]~_ >
  ass13 {f01 = f01}{f03}{f12}{f23} (v012 ^ v023)
    with f13 , v123 <- tri f12 f23
       | v013 ^ w023 <- ass03 (v012 ^ v123)
       | r~ <- triq (! v023) (! w023)
       = v013 ^ v123

module _ {X : Set}{A : X -> X -> Set}(C : Cat A)
         {Y : Set}{B : Y -> Y -> Set}(D : Cat B)
         where
  open Cat
  record Fun : Set where
    field
      fobj : X -> Y
      farr : forall {S T : X} -> A S T -> B (fobj S) (fobj T)
      fidq : (S : X) -> farr (iden C {S}) ~ iden D {fobj S}
      fcot : forall {R S T : X}{f : A R S}{g : A S T}{h : A R T}
          -> [_&_]~_ C f g h -> [_&_]~_ D (farr f) (farr g) (farr h)

module _ {O : Set}{A : O -> O -> Set} where
  open Cat
  _^op : Cat A -> Cat \ S T -> A T S
  iden (C ^op) = iden C
  [_&_]~_ (C ^op) f g h = [_&_]~_ C g f h
  tri (C ^op) f g = tri C g f
  triq (C ^op) v w = triq C v w
  idTri (C ^op) = triId C
  triId (C ^op) = idTri C
  ass03 (C ^op) (v ^ w) = let w' ^ v' = ass03 C (w ^ v) in v' ^ w'

module _ (X : Set) where
  open Cat
  Disc : Cat {X} _~_
  iden Disc = r~
  [_&_]~_ Disc _ _ _ = One
  tri Disc r~ q = q , <>
  triq Disc (r~ , <>) (r~ , <>) = r~
  idTri Disc = _
  triId Disc = _
  ass03 Disc {f01 = r~}{f02 = r~}{f23 = r~} _ = r~ , _

module _ {O : Set}{A : O -> O -> Set}(C : Cat A) where

  module _ where
    open Cat C
    data ConeObj : Set where
      limit : ConeObj
      copy  : O -> ConeObj
    data ConeArr : ConeObj -> ConeObj -> Set where
      limit : (o : ConeObj) -> ConeArr limit o
      copy  : forall {S T} -> A S T -> ConeArr (copy S) (copy T)
    data ConeTri : forall {R S T} -> ConeArr R S -> ConeArr S T -> ConeArr R T -> Set where
      copy  : forall {R S T}{f : A R S}{g : A S T}{h : A R T} -> [ f & g ]~ h
           -> ConeTri (copy f) (copy g) (copy h)
      limit : forall {S T}(f : ConeArr S T)
           -> ConeTri (limit S) f (limit T)
  open Cat
  Cone : Cat ConeArr
  iden Cone {limit} = limit limit
  iden Cone {copy x} = copy (iden C {x})
  [_&_]~_ Cone = ConeTri
  tri Cone (limit o)      g  = ! limit g
  tri Cone (copy f) (copy g) = let ! v = tri C f g in ! copy v
  triq Cone (! copy v) (! copy w) with r~ <- triq C (! v) (! w) = r~
  triq Cone (! limit f) (! limit .f) = r~
  idTri Cone (limit o) = limit (limit o)
  idTri Cone (copy f) = copy (idTri C f)
  triId Cone (limit o) = limit (iden Cone)
  triId Cone (copy f) = copy (triId C f)
  ass03 Cone (copy v ^ copy w) = let v' ^ w' = ass03 C (v ^ w) in copy v' ^ copy w'
  ass03 Cone (limit _ ^ _)     = limit _ ^ limit _

module _ {X : Set}{A : X -> X -> Set}{C : Cat A}
         {Y : Set}{B : Y -> Y -> Set}{D : Cat B}
         (F : Fun C D)
         where
  open Cat
  open Fun
  module _ where
    record ConeExt : Set where
      field
        limObj : Y
        limArr : (x : X) -> B limObj (fobj F x)
        limTri : forall {s t : X}(f : A s t)
              -> [_&_]~_ D (limArr s) (farr F f) (limArr t)
      ExtF : Fun (Cone C) D
      fobj ExtF limit    = limObj
      fobj ExtF (copy x) = fobj F x
      farr ExtF (limit limit)    = iden D
      farr ExtF (limit (copy x)) = limArr x
      farr ExtF (copy f)         = farr F f
      fidq ExtF limit    = r~
      fidq ExtF (copy x) = fidq F x
      fcot ExtF (copy v) = fcot F v
      fcot ExtF (limit (limit o)) = idTri D _
      fcot ExtF (limit (copy f)) = limTri f
    open ConeExt public
    record Limit : Set where
      field
        best   : ConeExt
        factor : (c : ConeExt) ->
          B (limObj c) (limObj best) >!< \ f ->
            (x : X) -> [_&_]~_ D f (limArr best x) (limArr c x)
    open Limit public

module _ {X : Set}{A : X -> X -> Set}(C : Cat A) where
  open Cat C
  open Fun
  Pair : X -> X -> Fun (Disc Two) C
  fobj (Pair S T) ff = S
  fobj (Pair S T) tt = T
  farr (Pair S T) {ff} r~ = iden
  farr (Pair S T) {tt} r~ = iden
  fidq (Pair S T) ff = r~
  fidq (Pair S T) tt = r~
  fcot (Pair S T) {ff} {f = r~} {g = r~} {h = r~} = \ _ -> idTri iden
  fcot (Pair S T) {tt} {f = r~} {g = r~} {h = r~} = \ _ -> idTri iden

  Products : Set
  Products = (S T : X) -> Limit (Pair S T)

module _ {X : Set}{_=>_ : X -> X -> Set}(C : Cat _=>_)(x : X) where
  open Cat C
  _//_ : Cat {< _=> x >}(\ (! f) (! g) -> < [_& g ]~ f > )
  Cat.iden _//_ = ! idTri _
  Cat.[_&_]~_ _//_ (f , _) (g , _) (h , _) = [ f & g ]~ h
  Cat.tri _//_ (f , v) (g , w) = let h , x , y = ass02 (v ^ w) in (h , y) , x
  Cat.triq _//_ ((f , v) , x) ((g , w) , y)
    with r~ <- triq (! x) (! y)
       | r~ <- triq (! v) (! w)
       = r~
  Cat.idTri _//_ (f , _) = idTri f
  Cat.triId _//_ (f , _) = triId f
  Cat.ass03 _//_ {X0 , f0}{X1 , f1}{X2 , f2}{X3 , f3}
                 {g01 , v01}{g02 , v02}{g23 , v23}{g13 , v13}
                 ((g12 , v12) , v012 , v123)
    with g03 , v012 , v023 <- ass03 (v012 ^ v123)
       | w01 ^ w <- ass03 (v012 ^ v13)
       | r~ <- triq (! v01) (! w01)
    = (g03 , w) , v012 , v023
    
module _ {X : Set}{_=>_ : X -> X -> Set} where
  _\\_ : (C : Cat _=>_)(x : X)
    -> Cat {< x =>_ >} (\ (! f) (! g) -> _ >< \ h -> Cat.[_&_]~_ C f h g)
  C \\ x = ((C ^op) // x) ^op


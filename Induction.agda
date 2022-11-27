module Induction where

data Zero : Set where
record One : Set where constructor <>
data Two : Set where ff tt : Two
record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_

record IxCon (I : Set) : Set1 where
  constructor _<!_/_
  field
    Shape     : I -> Set
    Position  : (i : I) -> Shape i -> Set
    offspring : (i : I)(s : Shape i)(p : Position i s) -> I
  _$_ : (I -> Set) -> (I -> Set)
  _$_ X i = Shape i >< \ s -> ((p : Position i s) -> X (offspring i s p))
  _$$_ : forall {X Y : I -> Set}
          -> (forall {i} -> X i -> Y i)
          -> forall {i} -> _$_ X i -> _$_ Y i
  _$$_ f (s , k) = s , \ p -> f (k p)
open IxCon

module _ {I : Set}(F : IxCon I) where

  data Mu (i : I) : Set where
    con : (F $ Mu) i -> Mu i

  iterate : forall {X : I -> Set}
         -> (forall {i} -> (F $ X) i -> X i)
         -> forall {i} -> Mu i -> X i
  iterate alg (con (s , k)) = alg (s , \ p -> iterate alg (k p))
  -- iterate alg (con fr) = alg ((F $$ iterate alg) fr)

  _^ : IxCon (I >< Mu)
  Shape     _^ _ = One
  Position  _^ (i , con (s , k)) <> = Position F i s
  offspring _^ (i , con (s , k)) <> p = offspring F i s p , k p

inductivity : forall {I}{F : IxCon I}
         -> forall {i}(x : Mu F i) -> Mu (F ^) (i , x)
inductivity (con (s , k)) = con (<> , \ p -> inductivity (k p))

induction : forall {I}{F : IxCon I}
         -> (P : forall i -> Mu F i -> Set)
         -> (forall {i}(s : Shape F i)
             (k : (p : Position F i s) -> Mu F (offspring F i s p))
             (h : (p : Position F i s) -> P (offspring F i s p) (k p))
            -> P i (con (s , k)))
         -> forall {i}(x : Mu F i) -> P i x
induction {F = F} P m x =
  iterate (F ^) {X = \ (i , x) -> P i x}
    (\ { {(i , con (s , k))} (<> , h) -> m s k h})
    (inductivity x)

NAT : IxCon One
Shape     NAT <> = Two
Position  NAT <>    ff = Zero
Position  NAT <>    tt = One
offspring NAT <>    tt    <> = <>

Nat = Mu NAT <>
ze : Nat
ze = con (ff , \ ())
su : Nat -> Nat
su n = con (tt , \ (<>) -> n)

_+_ : Nat -> Nat -> Nat
_+_ x y = iterate NAT (\ { (ff , _) -> y ; (tt , k) -> su (k <>) }) x

data _~_ {X : Set}(x : X) : X -> Set where
  r~ : x ~ x
postulate
  ext : forall {S : Set}{T : S -> Set}{f g : (s : S) -> T s}
    -> ((s : S) -> f s ~ g s)
    -> f ~ g
!~ : forall {X}(x : X) -> x ~ x
!~ x = r~
_~$~_ : forall {S T : Set}
        {f g : S -> T} -> f ~ g ->
        {x y : S} -> x ~ y ->
        f x ~ g y
r~ ~$~ r~ = r~

_+ze : (x : Nat) -> (x + ze) ~ x
x +ze = induction (\ _ x -> (x + ze) ~ x)
  (\ { ff k h -> !~ con ~$~ (!~ (ff ,_) ~$~ ext \ () )
     ; tt k h -> !~ con ~$~ (!~ (tt ,_) ~$~ ext \ _ -> h <>) })
  x

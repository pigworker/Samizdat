module JacoDay where

record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_ public
infixr 4 _,_
_*_ : Set -> Set -> Set
S * T = S >< \ _ -> T

data Zero : Set where
record One : Set where constructor <>
data Two : Set where ff tt : Two

_+_ : Set -> Set -> Set
S + T = Two >< \ { ff -> S ; tt -> T }

data Size : Set where
  ze un : Size
  _+S_ _*S_ : Size -> Size -> Size

[_]0 : Size -> Set -> Set
[ ze ]0 X = One
[ un ]0 X = X
[ N +S M ]0 X = [ N ]0 X * [ M ]0 X
[ N *S M ]0 X = [ N ]0 ([ M ]0 X)

pure : (N : Size) -> {X : Set} -> X -> [ N ]0 X
pure ze x = <>
pure un x = x
pure (N +S M) x = pure N x , pure M x
pure (N *S M) x = pure N (pure M x)

apply : (N : Size) -> {S T : Set} -> [ N ]0 (S -> T) -> [ N ]0 S -> [ N ]0 T
apply ze <> <> = <>
apply un f s = f s
apply (N +S M) (fs , gs) (ss , ts) = apply N fs ss , apply M gs ts
apply (N *S M) fs ss = apply N (apply N (pure N (apply M)) fs) ss

map : (N : Size) -> {S T : Set} -> (S -> T) -> [ N ]0 S -> [ N ]0 T
map N f = apply N (pure N f)

[_]P : Size -> Set
[ ze ]P = Zero
[ un ]P = One
[ N +S M ]P = [ N ]P + [ M ]P
[ N *S M ]P = [ N ]P * [ M ]P

D : (N : Size) -> [ N ]P -> Size
D un p = ze
D (N +S M) (ff , p) = D N p +S M
D (N +S M) (tt , p) = N +S D M p
D (N *S M) (p , q)  = (D N p *S D M q) +S (D N p +S D M q)

plug : {X : Set}(N : Size)(p : [ N ]P) -> [ D N p ]0 X -> X -> [ N ]0 X
plug un <> <> x = x
plug (N +S M) (ff , p) (p' , q) x = plug N p p' x , q
plug (N +S M) (tt , q) (p , q') x = p , plug M q q' x
plug (N *S M) (p , q) (m' , p' , q') x =
  apply N (apply N (pure N (plug M q))
    (plug N p m' q'))
    (plug N p p' x)

gulp : {X : Set}(N : Size)(p : [ N ]P) -> [ N ]0 X -> [ D N p +S un ]0 X
gulp un <> x = <> , x
gulp (N +S M) (ff , p) (xn , yn) with xn' , x <- gulp N p xn = (xn' , yn) , x
gulp (N +S M) (tt , q) (xn , yn) with yn' , y <- gulp M q yn = (xn , yn') , y
gulp (N *S M) (p , q) xmn
  with xmn' , xm <- gulp N p xmn
     | xm' , x <- gulp M q xm
     | xgn' <- map (D N p) (gulp M q) xmn'
     = (map (D N p) fst xgn' , map (D N p) snd xgn' , xm') , x

cart : {X Y : Set}(N M : Size) -> [ N ]0 X -> [ M ]0 Y -> [ N *S M ]0 (X * Y)
cart N M xn ym = map N (\ x -> map M (x ,_) ym) xn

[_]1 : (N : Size){X : Set}(P : X -> Set) -> [ N ]0 X -> Set
[ ze ]1 P <> = One
[ un ]1 P x = P x
[ N +S M ]1 P (xs , ys) = [ N ]1 P xs * [ M ]1 P ys
[ N *S M ]1 P xss = [ N ]1 ([ M ]1 P) xss

data _<=_ : Size -> Size -> Set where
  ze : forall {M} -> ze <= M
  un : un <= un
  _+S_ : forall {N N' M M'} -> N <= N' -> M <= M' -> (N +S M) <= (N' +S M')
  _*S_ : forall {N N' M M'} -> N <= N' -> M <= M' -> (N *S M) <= (N' *S M')

select : forall {N N' X} -> N <= N' -> [ N' ]0 X -> [ N ]0 X
select ze _ = <>
select un x = x
select (th +S ph) (xn , yn) = select th xn , select ph yn
select (_*S_ {N}{N'}{M}{M'} th ph) xn = select th (map N' (select ph) xn)

record _|>_ (I O : Set) : Set1 where
  constructor Cn
  field
    Sh : O -> Set
    Si : (o : O) -> Sh o -> Size
    Ch : (o : O)(s : Sh o) -> [ Si o s ]0 I
open _|>_

[_]C : forall {O I} -> I |> O -> (I -> Set) -> (O -> Set)
[ Cn S Z iz ]C X o = S o >< \ s -> [ Z o s ]1 X (iz o s)

data _~_ {X : Set}(x : X) : X -> Set where
  r~ : x ~ x

J : forall {I O : Set} -> I |> O -> I |> (I * O)
Sh (J (Cn S Z iz)) (i , o) = S o >< \ s -> [ Z o s ]P >< \ p -> snd (gulp (Z o s) p (iz o s)) ~ i
Si (J (Cn S Z iz)) (_ , o) (s , p , r~) = D (Z o s) p
Ch (J (Cn S Z iz)) (_ , o) (s , p , r~) = fst (gulp (Z o s) p (iz o s))

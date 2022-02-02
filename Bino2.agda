module Bino2 where

record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_
_*_ : Set -> Set -> Set
S * T = S >< \ _ -> T
pattern !_ t = _ , t
infixr 30 !_ _,_

module _ {X : Set} where

  <_> : (X -> Set) -> Set
  < P > = X >< P

  _*:_ : (X -> Set) -> (X -> Set) -> (X -> Set)
  (P *: Q) x = P x * Q x

  data _~_ (x : X) : X -> Set where
    r~ : x ~ x

  infix 20 _~_

  subst : forall {x y} -> x ~ y -> (P : X -> Set) -> P x -> P y
  subst r~ P p = p

  _~[_>_ : forall x {y z} -> x ~ y -> y ~ z -> x ~ z
  x ~[ r~ > q = q
  _<_]~_ : forall x {y z} -> y ~ x -> y ~ z -> x ~ z
  x < r~ ]~ q = q
  infixr 3 _~[_>_ _<_]~_
  _[QED] : forall x -> x ~ x
  x [QED] = r~
  infix 4 _[QED]

  !~_ : forall x -> x ~ x
  !~ x = r~
  infixl 6 !~_

{-# BUILTIN EQUALITY _~_ #-}

_~$~_ : forall {S T}{f g : S -> T}{x y : S}
     -> f ~ g -> x ~ y -> f x ~ g y
r~ ~$~ r~ = r~
infixl 5 _~$~_

data List (X : Set) : Set where
  []   : List X
  _,-_ : X -> List X -> List X

infixr 50 _,-_

data Nat : Set where
  ze : Nat
  su : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

data [_+_]~_ : Nat -> Nat -> Nat -> Set where
  ze+ : forall y -> [ ze + y ]~ y
  su  : forall {x y z} -> [ x + y ]~ z -> [ su x + y ]~ su z

add : forall x y -> < [ x + y ]~_ >
add ze y = y , ze+ y
add (su x) y = let ! z = add x y in ! su z
_+N_ : Nat -> Nat -> Nat
x +N y = fst (add x y)
infixr 60 _+N_

addU : forall {x y}(p q : < [ x + y ]~_ >) -> p ~ q
addU (! ze+ _) (! ze+ _) = r~
addU (! su p) (! su q) with r~ <- addU (! p) (! q) = r~

{-
func : List Nat -> Nat -> Nat
func []        x      = 0
func (n ,- ns) 0      = n
func (n ,- ns) (su x) = func ns x +N func (n ,- ns) x
-}

next : List Nat -> List Nat
next [] = []
next (n0 ,- []) = n0 ,- []
next (n0 ,- ns@(n1 ,- _)) = (n1 +N n0) ,- next ns

func : List Nat -> Nat -> Nat
func ns   (su x) = func (next ns) x
func (n ,- ns) 0 = n
func []        0 = 0

func[]0 : forall x -> func [] x ~ 0
func[]0 ze     = r~
func[]0 (su x) = func[]0 x

funk : forall n x -> func (n ,- []) x ~ n
funk n ze = r~
funk n (su x) = funk n x

diffFunc : forall n ns x -> func (n ,- ns) (su x) ~ func ns x +N func (n ,- ns) x
diffFunc n0 []         (su x) = 
  func (n0 ,- []) x < !~ _+N func (n0 ,- []) x ~$~ func[]0 x ]~
  func [] x +N func (n0 ,- []) x [QED]
diffFunc n0 (n1 ,- ns) (su x) = diffFunc (n1 +N n0) (next (n1 ,- ns)) x
diffFunc n0 []         ze = r~
diffFunc n0 (n1 ,- ns) ze = r~

infixl 80 _%_
_%_ : Nat -> Nat -> Nat
x % 0 = 1
0 % su _ = 0
su x % su n = x % n +N x % su n

data [_*_]~_ : Nat -> Nat -> Nat -> Set where
  ze* : forall n -> [ 0 * n ]~ 0
  su* : forall {x y z w} -> [ x * y ]~ z -> [ y + z ]~ w -> [ su x * y ]~ w

mul : forall x y -> < [ x * y ]~_ >
mul ze y = ! ze* y
mul (su x) y with z , m <- mul x y | w , a <- add y z = w , su* m a

infixr 70 _*N_
_*N_ : Nat -> Nat -> Nat
x *N y = fst (mul x y)

mulU : forall {x y}(p q : < [ x * y ]~_ >) -> p ~ q
mulU (! ze* n) (! ze* .n) = r~
mulU (! su* p a) (! su* q b)
  with r~ <- mulU (! p) (! q) | r~ <- addU (! a) (! b) = r~


_+N0 : forall x -> x +N 0 ~ x
ze +N0 = r~
su x +N0 = !~ su ~$~ x +N0

_+Nsu_ : forall x y -> x +N su y ~ su x +N y
ze +Nsu y = r~
su x +Nsu y = !~ su ~$~ x +Nsu y

asso+N : forall x y z -> (x +N y) +N z ~ x +N (y +N z)
asso+N ze y z = r~
asso+N (su x) y z = !~ su ~$~ asso+N x y z

comm+N : forall x y -> x +N y ~ y +N x
comm+N x ze = x +N0
comm+N x (su y) = 
  x +N su y ~[ x +Nsu y >
  su x +N y ~[ !~ su ~$~ comm+N x y >
  su y +N x [QED]

mid4+N : forall w x y z -> (w +N x) +N (y +N z) ~ (w +N y) +N (x +N z)
mid4+N w x y z =
  (w +N x) +N (y +N z) ~[ asso+N w x _ >
  w +N (x +N (y +N z))
    ~[ !~ w +N_ ~$~ (
    x +N y +N z < asso+N x y z ]~
    (x +N y) +N z ~[ !~ _+N z ~$~ comm+N x y >
    (y +N x) +N z ~[ asso+N y x z >
    y +N x +N z [QED]
    ) >
  w +N (y +N (x +N z)) < asso+N w y _ ]~
  (w +N y) +N (x +N z) [QED]


times0 : forall x -> x *N 0 ~ 0
times0 ze = r~
times0 (su x) = times0 x
times+N : forall x y z -> x *N (y +N z) ~ x *N y +N x *N z
times+N ze y z = r~
times+N (su x) y z = 
  (y +N z) +N x *N (y +N z) ~[ !~ (y +N z) +N_ ~$~ times+N x y z >
  (y +N z) +N (x *N y +N x *N z) ~[ mid4+N y z _ _ >
  (y +N x *N y) +N (z +N x *N z) [QED]

times1 : forall x -> x *N 1 ~ x
times1 ze = r~
times1 (su x) = !~ su ~$~ times1 x

plus*N : forall x y z -> (x +N y) *N z ~ x *N z +N y *N z
plus*N ze y z = r~
plus*N (su x) y z = 
  z +N (x +N y) *N z ~[ !~ z +N_ ~$~ plus*N x y z >
  z +N (x *N z +N y *N z) < asso+N z (x *N z) (y *N z) ]~
  (z +N x *N z) +N y *N z [QED]

asso*N : forall x y z -> (x *N y) *N z ~ x *N (y *N z)
asso*N ze y z = r~
asso*N (su x) y z = 
  (y +N x *N y) *N z ~[ plus*N y (x *N y) z >
  y *N z +N (x *N y) *N z ~[ !~ y *N z +N_ ~$~ asso*N x y z >
  y *N z +N x *N y *N z [QED]

bino : Nat -> List Nat -> Nat -> Nat
bino i [] x = 0
bino i (n ,- ns) x = n *N x % i +N bino (su i) ns x 

binoLem : forall i ns x -> bino (su i) ns (su x) ~ bino i ns x +N bino (su i) ns x
binoLem i [] x = r~
binoLem i (n ,- ns) x = 
  n *N (x % i +N x % su i) +N bino (su (su i)) ns (su x)
    ~[ !~ _+N_ ~$~ times+N n (x % i) (x % su i) ~$~ binoLem (su i) ns x >
  (n *N x % i +N n *N x % su i) +N (bino (su i) ns x +N bino (su (su i)) ns x)
    ~[ mid4+N (n *N x % i) (n *N x % su i) (bino (su i) ns x) (bino (su (su i)) ns x) >
  (n *N x % i +N bino (su i) ns x) +N
    (n *N x % su i +N bino (su (su i)) ns x) [QED]

bino1ns0 : forall i ns -> bino (su i) ns 0 ~ 0
bino1ns0 i [] = r~
bino1ns0 i (n ,- ns) = 
  n *N 0 +N bino (su (su i)) ns 0 ~[ !~ _+N_ ~$~ times0 n ~$~ bino1ns0 (su i) ns >
  0 [QED]

funcBino : forall ns x -> func ns x ~ bino 0 ns x
funcBino [] (su x) = func[]0 x
funcBino (n0 ,- ns) (su x) =
  func (n0 ,- ns) (su x) ~[ diffFunc n0 ns x >
  func ns x +N func (n0 ,- ns) x ~[ !~ _+N_ ~$~ funcBino ns x ~$~ funcBino (n0 ,- ns) x >
  bino 0 ns x +N bino 0 (n0 ,- ns) x ~[ mid4+N 0 (bino 0 ns x) (n0 *N 1) (bino 1 ns x) >
  n0 *N 1 +N bino 0 ns x +N bino 1 ns x < !~ n0 *N 1 +N_ ~$~ binoLem 0 ns x ]~
  bino 0 (n0 ,- ns) (su x) [QED]
funcBino [] 0 = r~
funcBino (n0 ,- ns) 0 = 
  n0 < n0 +N0 ]~
  n0 +N 0 < !~ _+N_ ~$~ times1 n0 ~$~ bino1ns0 0 ns ]~
  n0 *N 1 +N bino 1 ns ze [QED]


data Poly : Nat -> Set where
  X : forall {n} -> Poly (su n)
  # : forall {n} -> Nat -> Poly n
  _+P_ : forall {n} -> Poly n -> Poly n -> Poly n
  prod : forall {i j k} -> [ i + j ]~ k -> Poly i -> Poly j -> Poly k
infixr 20 _+P_

poly : forall {n} -> Poly n -> Nat -> Nat
poly X x = x
poly (# n) x = n
poly (p +P q) x = poly p x +N poly q x
poly (prod z p q) x = poly p x *N poly q x

$ : forall {n} -> Poly n -> Poly n
$ X = # 1 +P X
$ (# n) = # n
$ (p +P q) = $ p +P $ q
$ (prod z p q) = prod z ($ p) ($ q)

$ok : forall {n}(p : Poly n) x -> poly ($ p) x ~ poly p (su x)
$ok X x = r~
$ok (# n) x = r~
$ok (p +P q) x rewrite $ok p x | $ok q x = r~
$ok (prod z p q) x rewrite $ok p x | $ok q x = r~


diff : forall {n} -> Poly (su n) -> Poly n
diff X = # 1
diff (# x) = # 0
diff (p +P q) = diff p +P diff q
diff (prod {ze} {su j} {.(su _)} z p q) = prod (help z) p (diff q) where
  help : forall {j n} -> [ ze + su j ]~ su n -> [ ze + j ]~ n
  help (ze+ _) = ze+ _
diff (prod {su i} {ze} {.(su _)} z p q) = prod (help z) (diff p) q where
  help : forall {i n} -> [ su i + ze ]~ su n -> [ i + ze ]~ n
  help (su z) = z
diff (prod {su i} {su j} {.(su _)} z p q) =
  prod (help z) (diff p) q +P prod (kelp z) ($ p) (diff q)
  where
  help : forall {i j n} -> [ su i + su j ]~ su n -> [ i + su j ]~ n
  help (su z) = z
  kelp : forall {i j n} -> [ su i + su j ]~ su n -> [ su i + j ]~ n
  kelp (su (ze+ _)) = su (ze+ _)
  kelp (su (su z)) = su (kelp (su z))

constPolyLem : forall (p : Poly ze)(x y : Nat) -> poly p x ~ poly p y
constPolyLem (# n) x y = r~
constPolyLem (p +P q) x y rewrite constPolyLem p x y | constPolyLem q x y = r~
constPolyLem (prod (ze+ _) p q) x y rewrite constPolyLem p x y | constPolyLem q x y = r~


mulo : forall {i j k} -> [ i + j ]~ k -> Poly i -> Poly j -> Poly k
mulo z (p +P q) r = mulo z p r +P mulo z q r
mulo z p (q +P r) = mulo z p q +P mulo z p r
mulo z p q = prod z p q

mulok : forall {i j k}(z : [ i + j ]~ k)(p : Poly i)(q : Poly j) x
     -> poly (mulo z p q) x ~ poly (prod z p q) x
mulok z (p +P q) r x
  rewrite mulok z p r x
        | mulok z q r x
        | plus*N (poly p x) (poly q x) (poly r x)
        = r~
mulok z X (p +P q) x
  rewrite mulok z X p x
        | mulok z X q x
        | times+N x (poly p x) (poly q x)
        = r~
mulok z X X x = r~
mulok z X (# n) x = r~
mulok z X (prod _ _ _) x = r~
mulok z (# n) (p +P q) x
  rewrite mulok z (# n) p x
        | mulok z (# n) q x
        | times+N n (poly p x) (poly q x)
        = r~
mulok z (# n) X x = r~
mulok z (# n) (# _) x = r~
mulok z (# n) (prod _ _ _) x = r~
mulok z (prod y p q) (r +P s) x
  rewrite mulok z (prod y p q) r x
        | mulok z (prod y p q) s x
        | times+N (poly p x *N poly q x) (poly r x) (poly s x)
        = r~
mulok z (prod y p q) X x = r~
mulok z (prod y p q) (# _) x = r~
mulok z (prod y p q) (prod _ _ _) x = r~

monopoly : forall {n} -> Poly n -> Poly n
monopoly X = X
monopoly (# n) = # n
monopoly (p +P q) = monopoly p +P monopoly q
monopoly (prod z p q) = mulo z (monopoly p) (monopoly q)

monopolok : forall {n}(p : Poly n) x -> poly p x ~ poly (monopoly p) x
monopolok X x = r~
monopolok (# n) x = r~
monopolok (p +P q) x rewrite monopolok p x | monopolok q x = r~
monopolok (prod z p q) x
  rewrite mulok z (monopoly p) (monopoly q) x
        | monopolok p x | monopolok q x
        = r~

diffLem : forall {n}(p : Poly (su n)) x -> poly p (su x) ~ poly (diff p) x +N poly p x
diffLem X x = r~
diffLem (# n) x = r~
diffLem (p +P q) x
  rewrite diffLem p x | diffLem q x
  = mid4+N (poly (diff p) x) (poly p x) (poly (diff q) x) (poly q x)
diffLem (prod (ze+ _) p q) x
  rewrite diffLem q x | constPolyLem p (su x) x = times+N (poly p x) (poly (diff q) x) (poly q x)
diffLem (prod {j = ze} (su z) p q) x
  rewrite diffLem p x | constPolyLem q (su x) x = plus*N (poly (diff p) x) (poly p x) (poly q x)
diffLem (prod {j = su j} (su z) p q) x
  rewrite $ok p x
  | diffLem p x | diffLem q x
  | monopolok (prod (ze+ ze) (# (poly (diff p) x) +P # (poly p x))
                       (# (poly (diff q) x) +P # (poly q x))) ze
  | plus*N (poly (diff p) x) (poly p x) (poly (diff q) x)
  | comm+N (poly (diff p) x *N poly (diff q) x)
           (poly (diff p) x *N poly q x)
  | asso+N (poly (diff p) x *N poly q x)
           (poly (diff p) x *N poly (diff q) x)
           (poly p x *N poly (diff q) x +N poly p x *N poly q x)
  | asso+N (poly (diff p) x *N poly q x)
           (poly (diff p) x *N poly (diff q) x +N poly p x *N poly (diff q) x)
           (poly p x *N poly q x)
  | asso+N (poly (diff p) x *N poly (diff q) x) (poly p x *N poly (diff q) x)
           (poly p x *N poly q x)
  =
  r~

differ : forall {n}(p : Poly n) -> List Nat
differ' : forall n (p : Poly n) -> List Nat
differ {n} p = poly p 0 ,- differ' _ p
differ' ze p = []
differ' (su n) p = differ (diff p)

sum : (Nat -> Nat) -> (Nat -> Nat)
sum f ze = ze
sum f (su n) = f n +N sum f n

sumLem : forall n x -> sum (_% n) x ~ (x % su n)
sumLem n ze = r~
sumLem n (su x) = !~ (x % n +N_) ~$~ sumLem n x

funcSum : forall ns x -> sum (func ns) x ~ func (0 ,- ns) x 
funcSum ns ze = r~
funcSum ns (su x) = 
  func ns x +N sum (func ns) x ~[ !~ func ns x +N_ ~$~ funcSum ns x >
  func ns x +N func (0 ,- ns) x  < diffFunc 0 ns x ]~
  func (next (0 ,- ns)) x [QED]

polySumDiff : forall {n}(p : Poly (su n)) x -> poly p x ~ poly p 0 +N sum (poly (diff p)) x
polySumDiff p ze = poly p ze < _ +N0 ]~
           poly p 0 +N sum (poly (diff p)) 0 [QED]
polySumDiff p (su x) = 
  poly p (su x) ~[ diffLem p x >
  poly (diff p) x +N poly p x ~[ !~ poly (diff p) x +N_ ~$~ polySumDiff p x >
  poly (diff p) x +N poly p 0 +N sum (poly (diff p)) x < asso+N (poly (diff p) x) _ _ ]~
  (poly (diff p) x +N poly p 0) +N sum (poly (diff p)) x
    ~[ !~ _+N sum (poly (diff p)) x ~$~ comm+N (poly (diff p) x) (poly p 0) >
  (poly p 0 +N poly (diff p) x) +N sum (poly (diff p)) x
    ~[ asso+N (poly p 0) _ _ >
  poly p 0 +N sum (poly (diff p)) (su x) [QED]

polyFunc : forall {n}(p : Poly n) x -> func (differ p) x ~ poly p x
polyFunc {ze} p x = 
  func (poly p 0 ,- []) x ~[ funk (poly p 0) x >
  poly p 0 < constPolyLem p x 0 ]~
  poly p x [QED]
polyFunc {su n} p ze = r~
polyFunc {su n} p (su x) = 
  func (poly p 0 ,- differ (diff p)) (su x) ~[ diffFunc (poly p 0) (differ (diff p)) x >
  func (differ (diff p)) x +N func (differ p) x
    ~[ !~ _+N_ ~$~ polyFunc (diff p) x ~$~ polyFunc p x >
  poly (diff p) x +N poly p x < diffLem p x ]~
  poly p (su x) [QED]

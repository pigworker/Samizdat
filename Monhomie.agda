module Monhomie where

record One : Set where constructor void

data Two : Set where
  `0 `1 : Two

record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_
_*_ : Set -> Set -> Set
S * T = S >< \ _ -> T

id : forall {l}{X : Set l} -> X -> X
id x = x

_o-_ : forall {i j k}{A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k}
  (f : {a : A}(b : B a) -> C a b)(g : (a : A) -> B a)
  (a : A) -> C a (g a)
(f o- g) a = f (g a)
infixl 5 _o-_

not : Two -> Two
not `0 = `1
not `1 = `0

_&&_ : Two -> Two -> Two
`0 && _ = `0
`1 && b = b

eq2 : Two -> Two -> Two
eq2 `0 = not
eq2 `1 = id

_<0_1>_ : Two -> Two -> Two -> Two
b0 <0 `0 1> b1 = b0
b0 <0 `1 1> b1 = b1

eq2Elim : (e x : Two)(P : Two -> Two -> Set)
       -> (P (not e) `0)
       -> (P e `1)
       -> P x (eq2 e x)
eq2Elim `0 `0 P pd ps = ps
eq2Elim `0 `1 P pd ps = pd
eq2Elim `1 `0 P pd ps = pd
eq2Elim `1 `1 P pd ps = ps 

data _~_ {X : Set}(x : X) : X -> Set where
  r~ : x ~ x

{-# BUILTIN EQUALITY _~_ #-}

postulate
  ext : forall {S : Set}{T : S -> Set}{f g : (s : S) -> T s}
     -> ((s : S) -> f s ~ g s)
     -> f ~ g

s~ : forall {X : Set}{x y : X} -> x ~ y -> y ~ x
s~ r~ = r~

subst : {X : Set}(P : X -> Set){x y : X} -> x ~ y -> P x -> P y
subst P r~ p = p

module _ {X : Set}(x : X) where

  _~[_>_ : forall {y z} -> x ~ y -> y ~ z -> x ~ z
  _~[_>_ r~ = id
  _<_]~_ : forall {y z} -> y ~ x -> y ~ z -> x ~ z
  _<_]~_ r~ = id
  _[QED] : x ~ x
  _[QED] = r~

  infixr 0 _~[_>_ _<_]~_
  infixr 1 _[QED]
  
_~$~_ : forall {S T}{f g : S -> T}{a b : S}
     -> f ~ g -> a ~ b -> f a ~ g b
infixl 3 _~$~_
r~ ~$~ r~ = r~
_$~_ : forall {S T}(f : S -> T){a b : S}
     -> a ~ b -> f a ~ f b
infixl 3 _$~_
_$~_ f = _~$~_ (r~ {x = f})

eq2r : (b : Two) -> eq2 b b ~ `1
eq2r `0 = r~
eq2r `1 = r~

neq2 : (b : Two) -> eq2 b (not b) ~ `0
neq2 `0 = r~
neq2 `1 = r~

notnot : (b : Two) -> not (not b) ~ b
notnot `0 = r~
notnot `1 = r~

---------------------------------------------------------------------
data List (X : Set) : Set where
  [] : List X
  _,-_ : X -> List X -> List X

infixr 5 _,-_

Action : Set -> Set
Action X = X -> X

foldr : forall {S T} -> (S -> Action T) -> List S -> Action T
foldr one [] = id
foldr one (s ,- ss) = one s o- foldr one ss

foldrExt : forall {S T}(f g : S -> Action T)
  (q : forall s t -> f s t ~ g s t)
  (ss : List S)(t : T)
  -> foldr f ss t ~ foldr g ss t
foldrExt f g q [] t = r~
foldrExt f g q (s ,- ss) t = 
  f s (foldr f ss t) ~[ q s _ >
  g s (foldr f ss t) ~[ g s $~ foldrExt f g q ss t >
  g s (foldr g ss t) [QED]

_++_ : forall {X} -> List X -> Action (List X)
xs ++ ys = foldr _,-_ xs ys
infixr 10 _++_

foldr++ : forall {S T}(one : S -> Action T)(ss0 ss1 : List S)
  -> foldr one (ss0 ++ ss1) ~ (foldr one ss0 o- foldr one ss1)
foldr++ one [] ss1 = r~
foldr++ one (s ,- ss0) ss1 = one s o-_ $~ foldr++ one ss0 ss1

join : forall {X} -> List (List X) -> List X
join xss = foldr _++_ xss []

foldrJoin : forall {S T}(one : S -> Action T)(sss : List (List S))
  -> foldr one (join sss) ~ foldr (foldr one) sss
foldrJoin one [] = r~
foldrJoin one (ss ,- sss) = 
  foldr one (ss ++ join sss) ~[ foldr++ one ss (join sss) >
  (foldr one ss o- foldr one (join sss)) ~[ foldr one ss o-_ $~ foldrJoin one sss >
  (foldr one ss o- foldr (foldr one) sss) [QED]

sing : forall {X} -> X -> List X
sing x = x ,- []

list : forall {S T} -> (S -> T) -> List S -> List T
list {S}{T} f ss = foldr {T = List T} (_,-_ o- f) ss []

foldrMap : forall {R S T}(one : S -> Action T)(f : R -> S)(rs : List R)
  -> foldr one (list f rs) ~ foldr (one o- f) rs 
foldrMap one f [] = r~
foldrMap one f (r ,- rs) = one (f r) o-_ $~ foldrMap one f rs

mapMap : forall {R S T}(f : S -> T)(g : R -> S)(rs : List R)
  -> list f (list g rs) ~ list (f o- g) rs
mapMap f g rs = 
  list f (list g rs) ~[ foldrMap (_,-_ o- f) g rs ~$~ r~ >
  list (f o- g) rs [QED]

listId : forall {X}(xs : List X) -> list id xs ~ xs
listId [] = r~
listId (x ,- xs) = x ,-_ $~ listId xs

joinJoin : forall {X}(xsss : List (List (List X)))
  -> join (join xsss) ~ join (list join xsss)
joinJoin xsss =
  join (join xsss) ~[ foldrJoin _++_ xsss ~$~ r~ >
  foldr (foldr _++_) xsss []
    ~[ foldrExt (foldr _++_) (_++_ o- join)
       (\ xss xs -> 
         foldr _++_ xss xs < foldrJoin _,-_ xss ~$~ r~ ]~
         (join xss ++ xs) [QED])
       xsss []
    >
  foldr (_++_ o- join) xsss [] < foldrMap _++_ join xsss ~$~ r~ ]~
  join (list join xsss) [QED]

joinNatural : forall {S T}(f : S -> T)(ss : List (List S))
  -> list f (join ss) ~ join (list (list f) ss)
joinNatural f ss = 
  list f (join ss) ~[ foldrJoin (_,-_ o- f) ss ~$~ r~ >
  foldr (foldr (_,-_ o- f)) ss [] ~[ foldrExt (foldr (_,-_ o- f)) (_++_ o- list f)
    (\ ss ts -> 
       foldr (_,-_ o- f) ss ts < foldrMap _,-_ f ss ~$~ r~ ]~
       list f ss ++ ts [QED])
    ss [] >
  foldr (_++_ o- list f) ss [] < foldrMap _++_ (list f) ss ~$~ r~ ]~
  join (list (list f) ss) [QED]

record Mon (CR : Set) : Set where
  field
    crush : List CR -> CR
    crushJoin : (uss : List (List CR)) ->
      crush (join uss) ~ crush (list crush uss)
    crushSing : (u : CR) ->
      crush (sing u) ~ u
  neu : CR
  neu = crush []
  cat : CR -> CR -> CR
  cat x y = crush (x ,- y ,- [])
  crushcat : forall xs ys -> crush (xs ++ ys) ~ cat (crush xs) (crush ys)
  crushcat xs ys = 
    crush (xs ++ ys) ~[ crush $~ (foldr _,-_ xs $~ s~ (listId ys)) >
    crush (join (xs ,- ys ,- [])) ~[ crushJoin (xs ,- ys ,- []) >
    cat (crush xs) (crush ys) [QED]
  neucat : forall y -> cat neu y ~ y
  neucat y = 
    cat neu y < cat neu $~ crushSing y ]~
    cat neu (crush (sing y)) < crushJoin ([] ,- sing y ,- []) ]~
    crush (sing y) ~[ crushSing y >
    y [QED]
  catneu : forall x -> cat x neu ~ x
  catneu x = 
    cat x neu < cat $~ crushSing x ~$~ r~ ]~
    cat (crush (sing x)) neu < crushJoin (sing x ,- [] ,- []) ]~
    crush (sing x) ~[ crushSing x >
    x [QED]
  catcat : forall x y z -> cat (cat x y) z ~ cat x (cat y z)
  catcat x y z = 
    cat (cat x y) z < cat (cat x y) $~ crushSing z ]~
    cat (cat x y) (crush (sing z))
      < crushJoin (_ ,- _ ,- []) ]~
    crush (x ,- y ,- z ,- [])
      ~[ crushJoin (_ ,- _ ,- []) >
    cat (crush (sing x)) (cat y z) ~[ cat $~ crushSing x ~$~ r~ >
    cat x (cat y z) [QED]

record _-M>_ {S T : Set}(M : Mon S)(N : Mon T) : Set where
  open Mon
  field
    hom : S -> T
    com : (ss : List S) -> crush N (list hom ss) ~ hom (crush M ss)
open _-M>_

module _ {S T : Set}{M : Mon S}{N : Mon T} where
  open Mon N

  NEU : M -M> N
  hom NEU _ = neu
  com NEU [] = r~
  com NEU (s ,- ss) = 
    crush (neu ,- list (\ _ -> neu) ss) ~[ crushcat (sing neu) (list (\ _ -> neu) ss) >
    cat (crush (sing neu)) (crush (list (\ _ -> neu) ss)) ~[ cat $~ crushSing neu ~$~ r~ >
    cat neu (crush (list (λ _ → neu) ss)) ~[ neucat _ >
    crush (list (\ _ -> neu) ss) ~[ com NEU ss >
    neu [QED]

module _ {X : Set}{M : Mon X} where
  open Mon M
  ID : M -M> M
  hom ID = id
  com ID xs = crush $~ listId xs

module _ {R S T : Set}{M : Mon R}{N : Mon S}{O : Mon T}
  (F : M -M> N)(G : N -M> O)
  where
  open Mon

  _-M-_ : M -M> O
  hom _-M-_ = hom G o- hom F
  com _-M-_ rs = 
    crush O (list (hom G o- hom F) rs) < crush O $~ mapMap _ _ rs ]~
    crush O (list (hom G) (list (hom F) rs)) ~[ com G (list (hom F) rs) >
    hom G (crush N (list (hom F) rs)) ~[ hom G $~ com F rs >
    hom G (hom F (crush M rs)) [QED]

module _ {S : Set}
  (e : S)
  (c : S -> S -> S)
  (ec : (s : S) -> c e s ~ s)
  (ce : (s : S) -> c s e ~ s)
  (cc : (r s t : S) -> c (c r s) t ~ c r (c s t))
  where
  open Mon
  BINARY : Mon S
  crush BINARY ss = foldr c ss e 
  crushJoin BINARY sss = 
    foldr c (join sss) e ~[ foldrJoin c sss ~$~ r~ >
    foldr (foldr c) sss e ~[ foldrExt _ _ bubble sss e >
    foldr (c o- (\ ss -> foldr c ss e)) sss e < foldrMap c (\ ss -> foldr c ss e) sss  ~$~ r~ ]~
    foldr c (list (\ ss -> foldr c ss e) sss) e [QED]
    where
      bubble : forall ss s -> foldr c ss s ~ c (foldr c ss e) s
      bubble [] s = s~ (ec s)
      bubble (x ,- ss) s = 
        c x (foldr c ss s) ~[ c x $~ bubble ss s >
        c x (c (foldr c ss e) s)  < cc _ _ _ ]~
        c (c x (foldr c ss e)) s [QED]
  crushSing BINARY = ce

module _ where
  open Mon
  module _ {S T : Set}(M : Mon T)(f : S -> T)(g : T -> S)
    (gf : (s : S) -> g (f s) ~ s)
    (gcatfg : (t t' : T) -> g (cat M (f (g t)) (f (g t'))) ~ g (cat M t t'))
    where

    VIA : Mon S
    VIA = BINARY (g (neu M)) (\ s0 s1 -> g (cat M (f s0) (f s1)))
      (\ s -> g (cat M (f (g (neu M))) (f s))
                < g $~ (cat M _ $~ (f $~ gf s)) ]~
              g (cat M (f (g (neu M))) (f (g (f s))))
                ~[ gcatfg (neu M) (f s) >
              g (cat M (neu M) (f s))
                ~[ g $~ neucat M (f s) >
              g (f s)
                ~[ gf s >
              s [QED])
      (\ s -> g (cat M (f s) (f (g (neu M)))) < g $~ (cat M $~ (f $~ gf s) ~$~ r~) ]~
              g (cat M (f (g (f s))) (f (g (neu M)))) ~[ gcatfg _ _ >
              g (cat M (f s) (neu M)) ~[ g $~ catneu M _ >
              g (f s) ~[ gf s >
              s [QED])
      \ r s t -> 
        g (cat M (f (g (cat M (f r) (f s)))) (f t))
          < g $~ (cat M _ $~ (f $~ gf t)) ]~
        g (cat M (f (g (cat M (f r) (f s)))) (f (g (f t)))) ~[ gcatfg _ _ >
        g (cat M (cat M (f r) (f s)) (f t)) ~[ g $~ catcat M _ _ _ >
        g (cat M (f r) (cat M (f s) (f t))) < gcatfg _ _ ]~
        g (cat M (f (g (f r))) (f (g (cat M (f s) (f t)))))
          ~[ g $~ (cat M $~ (f $~ gf r) ~$~ r~) >
        g (cat M (f r) (f (g (cat M (f s) (f t))))) [QED]

module _ (X : Set) where
  open Mon
  
  LI : Mon (List X)
  crush LI = join
  crushJoin LI = joinJoin
  crushSing LI [] = r~
  crushSing LI (x ,- xs) = x ,-_ $~ crushSing LI xs

module _ (X : Set) where
  open Mon
  
  AC : Mon (Action X)
  crush AC = foldr id
  crushJoin AC fss = 
    foldr id (join fss) ~[ foldrJoin id fss >
    foldr (foldr id) fss < foldrMap id (foldr id) fss ]~
    foldr id (list (foldr id) fss) [QED]
  crushSing AC f = r~

module _ where
  open Mon

  UN : Mon One
  crush UN = _
  crushJoin UN _ = r~
  crushSing UN _ = r~

module _ (S : Set){T : Set}(M : Mon T) where
  open Mon

  PWISE : Mon (S -> T)
  crush PWISE fs s = crush M (list (\ f -> f s) fs)
  crushJoin PWISE fss = ext \ s -> 
    crush M (list (\ f -> f s) (join fss)) ~[ crush M $~ joinNatural (\ f -> f s) fss >
    crush M (join (list (list (\ f -> f s)) fss)) ~[ crushJoin M (list (list (\ f -> f s)) fss) >
    crush M (list (crush M) (list (list (\ f -> f s)) fss)) ~[ crush M $~ (
      list (crush M) (list (list (\ f -> f s)) fss) ~[ mapMap (crush M) (list \ f -> f s) fss >
      list (crush M o- list (\ f -> f s)) fss
        < mapMap (\ f -> f s) (\ fs s -> crush M (list (\ f -> f s) fs)) fss ]~
      list (\ f -> f s) (list (\ fs s -> crush M (list (\ f -> f s) fs)) fss) [QED]
      )>
    crush M
      (list (\ f -> f s)
       (list (\ fs s -> crush M (list (\ f -> f s) fs)) fss)) [QED]
  crushSing PWISE f = ext \ s -> crushSing M (f s)

module _ {S T : Set}{M : Mon T} where
  open Mon M

  KONST : M -M> PWISE S M
  hom KONST t _ = t
  com KONST ts = ext \ s -> crush $~ (
    (list (\ f -> f s) (list (\ t _ -> t) ts)) ~[ mapMap _ _ ts >
    list id ts ~[ listId ts >
    ts [QED])

module _ {R S : Set}{M : Mon S} where
  open Mon

  APP : R -> PWISE R M -M> M
  hom (APP r) f = f r 
  com (APP r) fs = r~

module _ R {S T : Set}{M : Mon S}(N : Mon T)(f : R -> M -M> N) where
  open Mon

  LAM : M -M> PWISE R N
  hom LAM s r = hom (f r) s
  com LAM ss = ext \ r -> 
    crush N (list (\ k -> k r) (list (\ s r -> hom (f r) s) ss))
      ~[ crush N $~ mapMap _ _ ss >
    crush N (list (hom (f r)) ss) ~[ com (f r) ss >
    hom (f r) (crush M ss) [QED]

  LIFT : PWISE R M -M> PWISE R N
  hom LIFT g r = hom (f r) (g r)
  com LIFT gs = ext \ r -> 
    crush N
      (list (\ k -> k r) (list (\ g r -> hom (f r) (g r)) gs))
      ~[ crush N $~ (_ ~[ mapMap _ _ gs > _ < mapMap _ _ gs ]~ _ [QED]) >
    crush N (list (hom (f r)) (list (\ k -> k r) gs))
      ~[ com (f r) (list (\ k -> k r) gs) >
    hom (f r) (crush M (list (\ k -> k r) gs)) [QED]

module _ {R S}(M : Mon R)(N : Mon S) where
  open Mon

  PAIR : Mon (R * S)
  crush PAIR mns = crush M (list fst mns) , crush N (list snd mns)
  crushJoin PAIR mnss = _,_
     $~ (crush M (list fst (join mnss)) ~[ crush M $~ joinNatural fst mnss >
         crush M (join (list (list fst) mnss)) ~[ crushJoin M (list (list fst) mnss) >
         crush M (list (crush M) (list (list fst) mnss))
           ~[ crush M $~ mapMap (crush M) (list fst) mnss >
         crush M (list (crush M o- list fst) mnss)
           < crush M $~ mapMap fst _ mnss ]~ 
         crush M
           (list fst
             (list (\ mns -> crush M (list fst mns) , crush N (list snd mns))
         mnss)) [QED])
    ~$~ ((crush N (list snd (join mnss)) ~[ crush N $~ joinNatural snd mnss >
         crush N (join (list (list snd) mnss)) ~[ crushJoin N (list (list snd) mnss) >
         crush N (list (crush N) (list (list snd) mnss))
           ~[ crush N $~ mapMap (crush N) (list snd) mnss >
         crush N (list (crush N o- list snd) mnss)
           < crush N $~ mapMap snd _ mnss ]~ 
         crush N
           (list snd
             (list (\ mns -> crush M (list fst mns) , crush N (list snd mns))
         mnss)) [QED]))
  crushSing PAIR (m , n) = _,_ $~ crushSing M m ~$~ crushSing N n

  FST : PAIR -M> M
  hom FST = fst
  com FST _ = r~

  SND : PAIR -M> N
  hom SND = snd
  com SND _ = r~

{-
module _ {R S}{M : Mon R}{N : Mon S} where
  open Mon

  module _ {X : Set} where
    SHARE : PAIR (PWISE X M) (PWISE X N) -M> PWISE X (PAIR M N)
    SHARE = {!!}
-}

module _ {R S T}{M : Mon R}{N : Mon S}{O : Mon T}(f : M -M> N)(g : M -M> O) where
  open Mon

  _&&&_ : M -M> PAIR N O
  hom _&&&_ r = hom f r , hom g r
  com _&&&_ rs = _,_
     $~ (crush N (list fst (list (\ r -> hom f r , hom g r) rs)) ~[ crush N $~ mapMap _ _ rs >
         crush N (list (hom f) rs) ~[ com f rs >
         hom f (crush M rs) [QED])
    ~$~ (crush O (list snd (list (\ r -> hom f r , hom g r) rs)) ~[ crush O $~ mapMap _ _ rs >
         crush O (list (hom g) rs) ~[ com g rs >
         hom g (crush M rs) [QED])

{-
or : Two -> Two -> Two
or `0 b = b
or `1 b = `1

or1 : (b : Two) -> or b `1 ~ `1
or1 `0 = r~
or1 `1 = r~

orOp : Two -> Two -> Action Two
orOp d `0 = id
orOp d `1 = or d o- not

orOp0 : (d x : Two) -> orOp d x `0 ~ x
orOp0 d `0 = r~
orOp0 d `1 = or1 d

module _  (d : Two) where

  open Mon

  FOO : Mon Two
  crush FOO xs = foldr (orOp d) xs `0
  crushJoin FOO xss = 
    crush FOO (join xss) ~[ {!!} >
    crush FOO (list (crush FOO) xss) [QED]
  crushSing FOO x = orOp0 d x
-}

module _ {S T : Set}(f : S -> T)(M : Mon T) where
  open Mon M
  
  free : LI S -M> M
  hom free = crush o- list f
  com free ss = 
    crush (list (crush o- list f) ss) < crush $~ mapMap crush (list f) ss ]~
    crush (list crush (list (list f) ss))
      < crushJoin (list (list f) ss) ]~
    crush (join (list (list f) ss)) < crush $~ joinNatural f ss ]~
    crush (list f (join ss)) [QED]

module _ {T : Set}(M : Mon T) where
  open Mon M
  itself : LI T -M> M
  hom itself = crush
  com itself ss = s~ (crushJoin ss)

module _ (B : Mon Two) where
  open Mon

  dual : Mon Two
  crush dual = not o- crush B o- list not
  crushJoin dual bss = not $~ ((
    crush B (list not (join bss)) ~[ crush B $~ joinNatural not bss >
    crush B (join (list (list not) bss)) ~[ crushJoin B (list (list not) bss) >
    crush B (list (crush B) (list (list not) bss)) ~[ crush B $~ mapMap (crush B) (list not) bss >
    crush B (list (crush B o- list not) bss) < crush B $~ foldrExt _ _ (
      \ s t -> _,- t $~ notnot _)
      bss [] ]~
    crush B (list (not o- not o- crush B o- list not) bss) < crush B $~ mapMap not _ bss ]~
    crush B (list not (list (not o- crush B o- list not) bss)) [QED]))
  crushSing dual b = 
    not (crush B (not b ,- []))
      ~[ not $~ crushSing B (not b) >
    not (not b) ~[ notnot b >
    b [QED]

  DUAL : B -M> dual
  hom DUAL = not
  com DUAL bs = not $~ (crush B $~ (
    list not (list not bs) ~[ mapMap not not bs >
    list (not o- not) bs ~[ foldrExt _ _ (\ s t -> _,- t $~ notnot s) bs [] >
    list id bs ~[ listId bs >
    bs [QED]))

module _ where

  ind : Two -> List One
  ind `0 = []
  ind `1 = sing void

  open Mon

  pop : LI Two -M> LI One
  pop = free ind (LI One)

  pos : List One -> Two
  pos n = foldr (\ _ _ -> `1) n `0

  OR : Mon Two
  OR = VIA (LI One) ind pos
    (\ { `0 -> r~ ; `1 -> r~ })
    \ { [] [] -> r~ ; [] (_ ,- _) -> r~ ; (_ ,- _) m -> r~ }

  odd : List One -> Two
  odd n = foldr (\ _ -> not) n `0

  oddind : (t : Two) -> odd (ind t) ~ t
  oddind `0 = r~
  oddind `1 = r~

  XOR : Mon Two
  XOR = VIA (LI One) ind odd
    oddind
    help
    where
    help : (t t' : List One) ->
      odd (cat (LI One) (ind (odd t)) (ind (odd t'))) ~
      odd (cat (LI One) t t')
    help [] t' = 
      odd (cat (LI One) [] (ind (odd t')))
        ~[ odd $~ neucat (LI One) (ind (odd t')) >
      odd (ind (odd t')) ~[ oddind (odd t') >
      odd t' < odd $~ neucat (LI One) t' ]~
      odd (cat (LI One) [] t') [QED]
    help (void ,- t) t' = 
      odd (cat (LI One) (ind (not (odd t))) (ind (odd t'))) ~[ gaah (odd t) (ind (odd t')) >
      not (odd (cat (LI One) (ind (odd t)) (ind (odd t')))) ~[ not $~ help t t' >
      not (odd (cat (LI One) t t')) [QED]
      where
      gaah : forall b n -> odd (cat (LI One) (ind (not b)) n)
                         ~ not (odd (cat (LI One) (ind b) n))
      gaah `0 n = r~
      gaah `1 n = s~ (notnot _)
{-
module _ {T : Set}(M : Mon T) where
  open Mon

  module _ {S : Set}(f : S -> T)(g : T -> S)
    (gf : (s : S) -> g (f s) ~ s)
    (fg : (ts : List T) -> g (crush M (list (f o- g) ts)) ~ g (crush M ts))
    where

    open _-M>_
    VIA : Mon S
    crush VIA = g o- hom (free f M)
    crushJoin VIA sss =
      g (crush M (list f (join sss))) < g $~ com (free f M) sss ]~
      g (crush M (list (crush M o- list f) sss))
        < fg (list (crush M o- list f) sss) ]~
      g (crush M (list (f o- g) (list (crush M o- list f) sss)))
        ~[ g $~ (crush M $~ mapMap _ _ sss) >
      g (crush M (list (f o- g o- crush M o- list f) sss))
        < g $~ (crush M $~ mapMap _ _ sss) ]~
      g (crush M (list f (list (g o- crush M o- list f) sss))) [QED]
    crushSing VIA s = 
      g (crush M (sing (f s))) ~[ g $~ crushSing M (f s) >
      g (f s) ~[ gf s >
      s [QED]
-}

module _ (e : Two) -- the neutral element
         (d : Two) -- the image of two "not e" values
  where
  open Mon
  
  monOp : Two -> Two -> Two
  monOp x y = (d <0 eq2 e y 1> x) <0 eq2 e x 1> y

  labs2 : forall y -> monOp e y ~ y
  labs2 y rewrite eq2r e = r~

  rabs2 : forall x -> monOp x e ~ x
  rabs2 x rewrite eq2r e = eq2Elim e x (\ x q -> (x <0 q 1> e) ~ x) r~ r~

  nono2 : monOp (not e) (not e) ~ d
  nono2 rewrite neq2 e = r~

  asso2 : forall x y z -> monOp (monOp x y) z ~ monOp x (monOp y z)
  asso2 x y z = eq2Elim e x (\ x q ->
    monOp ((d <0 eq2 e y 1> x) <0 q 1> y) z ~
    ((d <0 eq2 e (monOp y z) 1> x) <0 q 1> monOp y z))
    (eq2Elim e y (\ y q -> monOp (d <0 q 1> not e) z ~
      (d <0 eq2 e ((d <0 eq2 e z 1> y) <0 q 1> z) 1> not e))
      (eq2Elim e z (\ z q -> monOp d z ~ (d <0 eq2 e (d <0 q 1> not e) 1> not e))
        (eq2Elim e d (\ d q -> ((d <0 eq2 e (not e) 1> d) <0 q 1> not e) ~ (d <0 q 1> not e))
          ((not e <0 eq2 e (not e) 1> not e) ~[ not e <0_1> not e $~ neq2 e > not e [QED])
          r~)
        (eq2Elim e d (\ d q -> ((d <0 eq2 e e 1> d) <0 q 1> e) ~
           (d <0 eq2 e (not e) 1> not e))
         ((not e <0 eq2 e e 1> not e) ~[ not e <0_1> not e $~ eq2r e >
           not e < not e <0_1> not e $~ neq2 e ]~
           (not e <0 eq2 e (not e) 1> not e) [QED])
         (e < e <0_1> not e $~ neq2 e ]~ (e <0 eq2 e (not e) 1> not e) [QED])))
      (eq2Elim e z (\ z q -> monOp (not e) z ~ (d <0 q 1> not e))
        nono2
        (rabs2 (not e))))
    r~

  BO : Mon Two
  crush BO bs = foldr monOp bs e
  crushJoin BO uss = foldr monOp (join uss) e ~[ foldrJoin monOp uss ~$~ r~ >
    foldr (foldr monOp) uss e ~[ foldrExt _ _
      (\ bs b -> 
        foldr monOp bs b ~[ bubble bs b >
        monOp (foldr monOp bs e) b [QED])
      uss e >
    foldr (monOp o- (\ bs -> foldr monOp bs e)) uss e
      < foldrMap monOp (\ bs -> foldr monOp bs e) uss ~$~ r~ ]~
    foldr monOp (list (\ bs -> foldr monOp bs e) uss) e [QED]
    where
    bubble : forall bs b ->
        foldr monOp bs b ~
        monOp (foldr monOp bs e) b
    bubble [] b = s~ (labs2 b)
    bubble (x ,- bs) b = 
      monOp x (foldr monOp bs b) ~[ monOp x $~ bubble bs b >
      monOp x (monOp (foldr monOp bs e) b)
        < asso2 x _ b ]~
      monOp (monOp x (foldr monOp bs e)) b [QED]
  crushSing BO b = rabs2 b



{-
module _ where
  open Mon

  -- e is the neutral element
  -- d is the result of combining not e with itself

  monOp : Two -> Two -> Two -> Two -> Two
  monOp e d x y = (d <0 eq2 e y 1> x) <0 eq2 e x 1> y

  labs2 : forall e d y -> monOp e d e y ~ y
  labs2 e d y rewrite eq2r e = r~

  rabs2 : forall e d x -> monOp e d x e ~ x
  rabs2 e d x rewrite eq2r e = eq2Elim e x (\ x z -> (x <0 z 1> e) ~ x)
    r~
    r~

  lem : forall x y e -> (x <0 eq2 e (not e) 1> y) ~ x
  lem x y `0 = r~
  lem x y `1 = r~

  asso2 : forall e d x y z -> monOp e d (monOp e d x y) z ~ monOp e d x (monOp e d y z)
  asso2 e d x y z = eq2Elim e x
    (\ e x b -> monOp e d ((d <0 eq2 e y 1> x) <0 b 1> y) z
              ~ ((d <0 eq2 e (monOp e d y z) 1> x) <0 b 1> monOp e d y z))
    (\ e -> eq2Elim e y (\ e y b -> monOp e d (d <0 b 1> not e) z ~
      (d <0 eq2 e ((d <0 eq2 e z 1> y) <0 b 1> z) 1> not e))
      (\ e -> eq2Elim e z (\ e z b -> ((d <0 b 1> d) <0 eq2 e d 1> z) ~ (d <0 eq2 e (d <0 b 1> not e) 1> not e))
      (\ e -> r~)
      \ e -> eq2Elim e d (\ e d b -> forall r -> r ~ d -> (d <0 b 1> e) ~ r)
        (\ e r -> s~)
        (\ e r -> s~)
        (d <0 eq2 e (not e) 1> not e) (lem d (not e) e))
      \ e -> eq2Elim e z
        (\ e z b -> ((d <0 b 1> not e) <0 eq2 e (not e) 1> z) ~ (d <0 b 1> not e))
        (\ e -> lem d (not e) e)
        \ e -> lem (not e) e e)
    \ x -> r~

  -- factor via binary to listy monoid equivalence
  BO : Two -> Two -> Mon Two
  crush (BO e d) bs = foldr (monOp e d) bs e
  crushJoin (BO e d) uss = 
    foldr (monOp e d) (join uss) e ~[ foldrJoin (monOp e d) uss ~$~ r~ >
    foldr (foldr (monOp e d)) uss e ~[ foldrExt _ _
      (\ bs b -> 
        foldr (monOp e d) bs b ~[ bubble e d bs b >
        monOp e d (foldr (monOp e d) bs e) b [QED])
      uss e >
    foldr (monOp e d o- (\ bs -> foldr (monOp e d) bs e)) uss e
      < foldrMap (monOp e d) (\ bs -> foldr (monOp e d) bs e) uss ~$~ r~ ]~
    foldr (monOp e d) (list (\ bs -> foldr (monOp e d) bs e) uss) e [QED]
    where
    bubble : forall e d bs b ->
        foldr (monOp e d) bs b ~
        monOp e d (foldr (monOp e d) bs e) b
    bubble e d [] b = s~ (labs2 e d b)
    bubble e d (x ,- bs) b = 
      monOp e d x (foldr (monOp e d) bs b) ~[ monOp e d x $~ bubble e d bs b >
      monOp e d x (monOp e d (foldr (monOp e d) bs e) b)
        < asso2 e d x _ b ]~
      monOp e d ((monOp e d x o- foldr (monOp e d) bs) e) b [QED]
  crushSing (BO e d) b = rabs2 e d b
-}

-------------------------------------------------------------------

data Ki : Set where tp mn : Ki

data Ob  : Ki -> Set where
  Ac : Ob tp -> Ob mn
  Tw : Ob tp
  Bo : Two -> Two -> Ob mn
  Li : forall {k} -> Ob tp -> Ob k
  _=>_ : forall {k} -> Ob tp -> Ob k -> Ob k
  Un : forall {k} -> Ob k
  _**_ : forall {k} -> Ob k -> Ob k -> Ob k

CR : Ob mn -> Ob tp
CR (Ac X) = X => X
CR (Bo b d) = Tw
CR (Li X) = Li X
CR (S => M) = S => CR M
CR Un = Un
CR (M ** N) = CR M ** CR N

TY : Ob tp -> Set
TY Tw = Two
TY (Li X) = List (TY X)
TY (S => T) = TY S -> TY T
TY Un = One
TY (R ** S) = TY R * TY S

open Mon

MN : (M : Ob mn) -> Mon (TY (CR M))
MN (Ac X) = AC (TY X)
MN (Bo e d) = BO e d
MN (Li X) = LI (TY X)
MN (S => M) = PWISE (TY S) (MN M)
MN Un = UN
MN (M ** N) = PAIR (MN M) (MN N)

data Bwd (X : Set) : Set where
  [] : Bwd X
  _-,_ : Bwd X -> X -> Bwd X
infixl 5 _-,_

data _<-_ {X : Set}(x : X) : Bwd X -> Set where
  ze : forall {xz} -> x <- (xz -, x)
  su : forall {xz}{y} -> x <- xz -> x <- (xz -, y)

bwd : forall {X Y} -> (X -> Y) -> Bwd X -> Bwd Y
bwd f [] = []
bwd f (xz -, x) = bwd f xz -, f x

tup : forall {k} -> Bwd (Ob k) -> Ob k
tup [] = Un
tup (Xz -, X) = tup Xz ** X

data _/_!-_ (De : Bwd (Ob mn))(Ga : Bwd (Ob tp)) : Ob tp -> Set
data _/_!=_ (De : Bwd (Ob mn))(Ga : Bwd (Ob tp)) : Ob mn -> Set

data _/_!-_ De Ga where
  tv : forall {T} -> T <- Ga -> De / Ga !- T
  ho : forall {M} -> De / Ga != M -> De / Ga !- CR M

data _/_!=_ De Ga where
  mv : forall {M} -> M <- De -> De / Ga != M
  ne : forall {M} -> De / Ga != M
  cr : forall {X M} -> De / Ga != Li X -> [] / Ga !- (X => CR M) -> De / Ga != M
  _&h_ : forall {M N} -> De / Ga != M -> De / Ga != N -> De / Ga != (M ** N)
  la : forall {S M} -> De / (Ga -, S) != M -> De / Ga != (S => M)
  ap : forall {S M} -> De / Ga != (S => M) -> [] / Ga !- S -> De / Ga != M

tpr : forall {Ga T} -> T <- Ga -> TY (tup Ga) -> TY T
tpr ze (_ , t) = t
tpr (su x) (ga , _) = tpr x ga

mpr : forall {De M} -> M <- De -> MN (tup De) -M> MN M
mpr {De -, M} ze     = SND (MN (tup De)) (MN M)
mpr {De -, N} (su x) = FST (MN (tup De)) (MN N) -M- mpr x

[!_!]ty : forall {De}{Ga}{T} -> De / Ga !- T -> TY (CR (tup De)) -> TY (tup Ga) -> TY T
[!_!]mh : forall {De}{Ga}{M} -> De / Ga != M -> MN (tup De) -M> PWISE (TY (tup Ga)) (MN M)

[! tv x !]ty de ga = tpr x ga
[! ho h !]ty de ga = hom [! h !]mh de ga

[! mv x !]mh = mpr x -M- KONST
[! ne !]mh = NEU
[!_!]mh {M = M} (cr l d) = [! l !]mh -M- LIFT _ _ \ ga -> free ([! d !]ty void ga) (MN M)
[! _&h_ {M} {N} h k !]mh = LAM _ (PAIR (MN M) (MN N)) \ ga ->
  ([! h !]mh -M- APP {M = MN M} ga) &&& ([! k !]mh -M- APP {M = MN N} ga)
hom [! la b !]mh = \ de ga s -> hom [! b !]mh de (ga , s)
com ([!_!]mh {De} (la {M = M} b)) des = ext \ ga -> ext \ s ->
  crush (MN M)
      (list (\ f -> f s)
       (list (\ f -> f ga)
        (list (\ de ga s -> hom [! b !]mh de (ga , s)) des)))
      ~[ crush (MN M) $~
        (_ ~[ list (\ f -> f s) $~ mapMap _ _ des > _ ~[ mapMap _ _ des >
           list (\ a -> hom [! b !]mh a (ga , s)) des
           < mapMap _ _ des ]~ _ [QED]) >
  crush (MN M) (list (\ f -> f (ga , s)) (list (hom [! b !]mh) des))
      ~[ com [! b !]mh des ~$~ r~ >
  hom [! b !]mh (crush (MN (tup De)) des) (ga , s) [QED]
[!_!]mh {De} {Ga} {M = M} (ap h s) = LAM (TY (tup Ga)) (MN M) \ ga -> [! h !]mh -M- (APP ga -M- APP ([! s !]ty void ga))

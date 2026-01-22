module Tree-Four where

module _ {X : Set} where

  data _~_ (x : X) : X -> Set where
    r~ : x ~ x

  _~[_>_ : forall x {y z} -> x ~ y -> y ~ z -> x ~ z
  x ~[ r~ > q = q

  _<_]~_ : forall x {y z} -> y ~ x -> y ~ z -> x ~ z
  x < r~ ]~ q = q

  rf _[QED] : forall x -> x ~ x
  rf x = r~
  x [QED] = r~

  infixr 2 _~[_>_ _<_]~_
  infixr 3 _[QED]

  subst : {x y : X}(P : X -> Set) -> P x -> x ~ y -> P y
  subst P p r~ = p

_~$~_ : forall {S T}
     {f g : S -> T} -> f ~ g
  -> {a b : S} -> a ~ b
  -> f a ~ g b
r~ ~$~ r~ = r~
infixl 4 _~$~_


data Tree (X : Set) : Set where
  [_] : X -> Tree X
  leaf : Tree X
  _/\_ : Tree X -> Tree X -> Tree X

_>>=_ : {X Y : Set} -> Tree X -> (X -> Tree Y) -> Tree Y
[ x ] >>= k = k x
leaf >>= k = leaf
(s /\ t) >>= k = (s >>= k) /\ (t >>= k)

_>>=[] : {X : Set}(t : Tree X) -> (t >>= [_]) ~ t
[ x ] >>=[] = r~
leaf >>=[] = r~
(s /\ t) >>=[] = rf _/\_ ~$~ (s >>=[]) ~$~ (t >>=[])

compo : forall {X Y Z}(f : X -> Tree Y)(g : Y -> Tree Z)(h : X -> Tree Z)
  -> (q : (x : X) -> (f x >>= g) ~ h x)
  -> (t : Tree X) -> ((t >>= f) >>= g) ~ (t >>= h)
compo f g h q [ x ] = q x
compo f g h q leaf = r~
compo f g h q (s /\ t) = rf _/\_ ~$~ compo f g h q s ~$~ compo f g h q t

data Zero : Set where
record One : Set where constructor <>
data Two : Set where ff tt : Two

noughtE : forall {l}{X : Set l}(x : Zero) -> X
noughtE ()

_<ft>_ : forall {l}{P : Two -> Set l} -> P ff -> P tt -> (b : Two) -> P b
(f <ft> t) ff = f
(f <ft> t) tt = t

inflate : {X : Set} -> Tree Zero -> Tree X
inflate t = t >>= noughtE

inflated : {X Y : Set}(t : Tree Zero)(f : X -> Tree Y) -> (inflate t >>= f) ~ inflate t
inflated t f =
  (inflate t >>= f) ~[ compo noughtE f noughtE (\ ()) t >
  inflate t [QED]

_&&_ : Two -> Two -> Two
ff && b = ff
tt && b = b

sbst2 : forall {X} -> Tree Two -> Tree X -> Tree X -> Tree X
sbst2 n s t = n >>= (s <ft> t)

xform : forall {X} -> Tree X -> Tree Two -> Tree Zero -> Tree X
xform l n leaf = l
xform l n (s /\ t) = sbst2 n (xform l n s) (xform l n t)

degeneracy : forall {X}(l : Tree X)(n : Tree Two)
  -> xform l n (leaf /\ leaf) ~ xform l n leaf
  -> (t : Tree Zero) -> xform l n t ~ l
degeneracy l n q leaf = r~
degeneracy l n q (s /\ t) = 
  xform l n (s /\ t) ~[ r~ >
  sbst2 n (xform l n s) (xform l n t)
    ~[ rf (sbst2 n) ~$~ degeneracy l n q s ~$~ degeneracy l n q t >
  sbst2 n l l ~[ q >
  l [QED]

record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_ public
_*_ _+_ : Set -> Set -> Set
S * T = S >< \ _ -> T
S + T = Two >< (S <ft> T)
infixr 5 _,_

_#_ : Tree Zero -> Tree Zero -> Set
leaf # leaf = Zero
leaf # (_ /\ _) = One
(_ /\ _) # leaf = One
(al /\ ar) # (bl /\ br) = (al # bl) + (ar # br)

kaboom : forall {a b : Tree Zero} -> a ~ b -> a # b -> forall {l}{X : Set l} -> X
kaboom {a /\ b} r~ (ff , n) = kaboom r~ n
kaboom {a /\ b} r~ (tt , n) = kaboom r~ n

_=?=_ : (a b : Tree Zero) -> (a # b) + (a ~ b)
leaf =?= leaf = tt , r~
leaf =?= (_ /\ _) = ff , <>
(_ /\ _) =?= leaf = ff , <>
(al /\ ar) =?= (bl /\ br) with al =?= bl | ar =?= br
... | ff , ap | bx , bp = ff , ff , ap
... | tt , ap | ff , bp = ff , tt , bp
... | tt , ap | tt , bp = tt , (rf _/\_ ~$~ ap ~$~ bp)

TreeNoConf : {X : Set} -> Tree X -> Tree X -> Set
TreeNoConf [ x ] [ y ] = x ~ y
TreeNoConf leaf leaf = One
TreeNoConf (al /\ ar) (bl /\ br) = (al ~ bl) * (ar ~ br)
TreeNoConf _ _ = Zero

treeNoConf : {X : Set}{a b : Tree X}(q : a ~ b) -> TreeNoConf a b
treeNoConf {X} {[ x ]} r~ = r~
treeNoConf {X} {leaf} r~ = <>
treeNoConf {X} {al /\ ar} r~ = r~ , r~


data Bwd (X : Set) : Set where
  [] : Bwd X
  _-,_ : Bwd X -> X -> Bwd X

data Fwd (X : Set) : Set where
  [] : Fwd X
  _,-_ : X -> Fwd X -> Fwd X

_<><_ : {X : Set} -> Bwd X -> Fwd X -> Bwd X
xz <>< [] = xz
xz <>< (x ,- xs) = (xz -, x) <>< xs

_<>>_ : {X : Set} -> Bwd X -> Fwd X -> Fwd X
[] <>> xs = xs
(xz -, x) <>> xs = xz <>> (x ,- xs)

_>>>_ : {X : Set} -> Fwd X -> Fwd X -> Fwd X
[] >>> ys = ys
(x ,- xs) >>> ys = x ,- (xs >>> ys)

DTree : Set -> Set
DTree X = Two * Tree X

upTree : {X : Set} -> DTree X -> Tree X -> Tree X
upTree (ff , x) s = s /\ x
upTree (tt , x) s = x /\ s

TZ : Set -> Set
TZ X = Bwd (DTree X)

zsub : {X Y : Set} -> TZ X -> (X -> Tree Y) -> TZ Y
zsub [] k = []
zsub (z -, (b , t)) k = zsub z k -, (b , (t >>= k))

gulp : {X : Set} -> TZ X -> Tree X -> Tree X
gulp [] t = t
gulp (lz -, l) t = gulp lz (upTree l t)

zsub-gulp : {X Y : Set}(z : TZ X)(t : Tree X)(k : X -> Tree Y)
  -> (gulp z t >>= k) ~ gulp (zsub z k) (t >>= k)
zsub-gulp [] t k = r~
zsub-gulp (z -, (ff , s)) t k = zsub-gulp z (t /\ s) k
zsub-gulp (z -, (tt , s)) t k = zsub-gulp z (s /\ t) k

TS : Set -> Set
TS X = Fwd (DTree X)

plug : {X : Set} -> TS X -> Tree X -> Tree X
plug [] t = t
plug (l ,- ls) t = upTree l (plug ls t)

gulp-fish : {X : Set} -> (lz : TZ X)(ls : TS X)(t : Tree X)
  -> gulp lz (plug ls t) ~ gulp (lz <>< ls) t
gulp-fish lz [] t = r~
gulp-fish lz (l ,- ls) t = gulp-fish (lz -, l) ls t

plug-chips : {X : Set} -> (lz : TZ X)(ls : TS X)(t : Tree X)
  -> gulp lz (plug ls t) ~ plug (lz <>> ls) t
plug-chips [] ls t = r~
plug-chips (lz -, l) ls t = plug-chips lz (l ,- ls) t

plug-cat : {X : Set}(ls ms : TS X)(t : Tree X) ->
  plug (ls >>> ms) t ~ plug ls (plug ms t)
plug-cat [] ms t = r~
plug-cat (x ,- ls) ms t = rf (upTree x) ~$~ plug-cat ls ms t

cat-nil : {X : Set}(xs ys : Fwd X) -> (xs >>> ys) ~ [] ->
  (xs ~ []) * (ys ~ [])
cat-nil [] ys q = r~ , q

chips-nil : {X : Set}(xz : Bwd X)(xs : Fwd X)
  -> (xz <>> xs) ~ []
  -> (xz ~ []) * (xs ~ [])
chips-nil [] xs q = r~ , q
chips-nil (xz -, x) xs q
  with _ , () <- chips-nil xz (x ,- xs) q

plug-nocy : {X : Set}(ls : TS X)(s : Tree X)
  -> plug ls s ~ s
  -> ls ~ []
plug-nocy [] s q = r~
plug-nocy ((ff , x) ,- ls) (sa /\ sb) q
  with ql , qr <- treeNoConf q
  with bad <- plug-nocy (ls >>> ((ff , sb) ,- [])) sa (
    plug (ls >>> ((ff , sb) ,- [])) sa ~[ plug-cat ls (_ ,- []) sa >
    plug ls (sa /\ sb) ~[ ql >
    sa [QED])
  with _ , () <- cat-nil ls (_ ,- []) bad
plug-nocy ((tt , x) ,- ls) (sa /\ sb) q with ql , qr <- treeNoConf q
  with bad <- plug-nocy (ls >>> ((tt , sa) ,- [])) sb (
    plug (ls >>> ((tt , sa) ,- [])) sb ~[ plug-cat ls (_ ,- []) sb >
    plug ls (sa /\ sb) ~[ qr >
    sb [QED])
  with _ , () <- cat-nil ls (_ ,- []) bad

gulp-nocy : {X : Set}(lz : TZ X)(s : Tree X)
  -> gulp lz s ~ s
  -> lz ~ []
gulp-nocy lz s q
  with q <- plug-nocy (lz <>> []) s ((
    plug (lz <>> []) s < plug-chips lz [] s ]~
    gulp lz s ~[ q >
    s [QED]))
  = fst (chips-nil lz [] q)



unsub : {X : Set}(z : TZ Zero)(k : X -> Tree Zero)(t : Tree X)
  -> ((x : X) -> gulp z (t >>= k) ~ k x)
  -> (t ~ inflate (t >>= k))
   + ((z ~ []) * (X >< \ x -> t ~ [ x ]))
unsub [] k [ x ] q = tt , r~ , x , r~
unsub (z -, l) k [ x ] q with () <- gulp-nocy (z -, l) _ (q x)
unsub z k leaf q = ff , r~
unsub z k (tl /\ tr) q
  with unsub (z -, (ff , _)) k tl q | unsub (z -, (tt , _)) k tr q
... | ff , x | ff , y = ff , (rf _/\_ ~$~ x ~$~ y)

jiggle : (l n s t : Tree Zero) -> Tree Two
jiggle l n s t with l =?= n | l =?= s | l =?= t
jiggle l n s t | tt , _ | ff , _ | _ = [ ff ]
jiggle l n s t | tt , _ | _ | ff , _ = [ tt ]
jiggle l n s t | tt , _ | tt , _ | tt , _ = inflate n
jiggle l leaf s t | ff , _ | _ | _ = leaf
jiggle l (nl /\ nr) (sl /\ sr) (tl /\ tr) | ff , _ | _ | _ =
  jiggle l nl sl tl /\ jiggle l nr sr tr
jiggle l (nl /\ nr) s t | ff , _ | _ | _ = inflate (nl /\ nr) 

wiggle : (Tree Zero -> Tree Zero) -> (Tree Zero -> Tree Zero)
wiggle f = xform (f leaf)
  (jiggle (f leaf)
    (f (leaf /\ leaf))
    (f ((leaf /\ leaf) /\ leaf))
    (f (leaf /\ (leaf /\ leaf))))

kontree : {X : Set}(c : Tree Zero)(t : Tree X)
  (f g : X -> Tree Zero)
  -> t ~ inflate c
  -> (t >>= f) ~ (t >>= g)
kontree c t f g r~ = 
   ((c >>= noughtE) >>= f) ~[ compo noughtE f [_] (\ ()) c >
   (c >>= [_]) < compo noughtE g [_] (\ ()) c ]~
   ((c >>= noughtE) >>= g) [QED]

jigglem : (l : Tree Zero)(z : TZ Two)(n : Tree Two)
  -> let t = gulp z n in
     let f = xform l t in let fl = f leaf in
     let fnll = f (leaf /\ leaf) in
     fl # fnll
  -> jiggle fl (n >>= (fl <ft> fl))
       (n >>= (fnll <ft> fl))
       (n >>= (fl <ft> fnll))
     ~ n
jigglem l z n a with l =?= (n >>= (l <ft> l))
... | tt , x with l =?= (n >>= ((gulp z n >>= (l <ft> l)) <ft> l))
                | l =?= (n >>= (l <ft> (gulp z n >>= (l <ft> l))))
                | unsub [] (l <ft> l) n
                  ((_ < x ]~ r~) <ft> (_ < x ]~ r~))
jigglem l z n a | tt , x | ff , y | c , w | ff , v =
  kaboom x (subst (l #_) y (kontree (n >>= (l <ft> l)) n
           ((gulp z n >>= (l <ft> l)) <ft> l) (l <ft> l) v))
jigglem l z n a | tt , x | ff , y | c , w | tt , _ , ff , r~ = r~
jigglem l z n a | tt , x | ff , y | ff , w | tt , r~ , tt , r~
  = kaboom x y
jigglem l z n a | tt , x | ff , y | tt , w | tt , r~ , tt , r~
  = kaboom x y
jigglem l z n a | tt , x | tt , y | ff , w | ff , v = 
  kaboom x (subst (l #_) w (kontree (n >>= (l <ft> l)) n
    (l <ft> (gulp z n >>= (l <ft> l))) (l <ft> l) v))
jigglem l z n a | tt , x | tt , y | ff , w | tt , _ , ff , r~
  = kaboom x w
jigglem l z n a | tt , x | tt , y | ff , w | tt , _ , tt , r~ = r~
jigglem l z n a | tt , x | tt , y | tt , w | ff , v = _ < v ]~ r~
jigglem l z n a | tt , x | tt , y | tt , w | tt , _ , ff , r~
  = kaboom y a
jigglem l z n a | tt , x | tt , y | tt , w | tt , _ , tt , r~
  = kaboom w a
jigglem l z [ ff ] a | ff , x = kaboom r~ x
jigglem l z [ tt ] a | ff , x = kaboom r~ x
jigglem l z leaf a | ff , x = r~
jigglem l z (ns /\ nt) a | ff , x
  = rf _/\_ ~$~ jigglem l (z -, (ff , nt)) ns a
            ~$~ jigglem l (z -, (tt , ns)) nt a


claim : (l : Tree Zero)(n : Tree Two)(t : Tree Zero) ->
    (xform l n leaf # xform l n (leaf /\ leaf))
  + (xform l n leaf ~ xform l n (leaf /\ leaf))
  -> wiggle (xform l n) t ~ xform l n t
claim l n t (ff , x) = 
  xform l
      (jiggle l (n >>= (l <ft> l)) (n >>= ((n >>= (l <ft> l)) <ft> l))
       (n >>= (l <ft> (n >>= (l <ft> l)))))
      t
      ~[ rf (\ n -> xform l n t) ~$~ jigglem l [] n x >
  xform l n t [QED]
claim l n t (tt , x) with l =?= (n >>= (l <ft> l))
... | ff , y = kaboom x y
... | tt , y with l =?= (n >>= ((n >>= (l <ft> l)) <ft> l))
       | l =?= (n >>= (l <ft> (n >>= (l <ft> l))))
... | ff , z | c , w = 
  xform l [ ff ] t ~[ degeneracy l [ ff ] r~ t >
  l < degeneracy l n  (_ < x ]~ r~) t ]~
  xform l n t [QED]
... | tt , z | ff , w = 
  xform l [ tt ] t ~[ degeneracy l [ tt ] r~ t >
  l < degeneracy l n  (_ < x ]~ r~) t ]~
  xform l n t [QED]
... | tt , z | tt , w =
  xform l (inflate (n >>= (l <ft> l))) t
    ~[ degeneracy l (inflate (n >>= (l <ft> l))) (
        sbst2 (inflate (n >>= (l <ft> l))) l l
          < rf (\ k -> sbst2 (inflate k) l l) ~$~ x  ]~
        sbst2 (inflate l) l l
          ~[ compo noughtE (l <ft> l) [_] (\ ()) l >
        l >>= [_] ~[ l >>=[] >
        l [QED]) t >
  l < degeneracy l n  (_ < x ]~ r~) t ]~
  xform l n t [QED]
  
fact : (l : Tree Zero)(n : Tree Two)(t : Tree Zero)
    -> wiggle (xform l n) t ~ xform l n t
fact l n t = claim l n t (l =?= sbst2 n l l)

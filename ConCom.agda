module ConCom where

data _~_ {l}{X : Set l}(x : X) : X -> Set l where
  r~ : x ~ x

-- see you B, raise you S
_-_ : forall {i j k}
      {A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k}
      (f : (a : A) -> B a)
      (g : {a : A}(b : B a) -> C a b)
      (a : A) -> C a (f a)
(f - g) a = g (f a)

infixl 10 _-_

record One : Set where constructor <>

record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_
infixr 5 _,_

record Con : Set1 where
  constructor _<!_
  field
    Sh : Set
    Po : Sh -> Set  -- datoid?
open Con

[_]o : Con -> Set -> Set
[ S <! P ]o X = S >< \ s -> P s -> X

[_]m : (F : Con){S T : Set} -> (S -> T) -> ([ F ]o S -> [ F ]o T)
[ F ]m f (s , k) = s , (k - f)

Div : Con -> Con
Div (S <! P) = (S >< P) <! (fst - P)

_=>_ : Con -> Con -> Set
(S <! P) => F = (s : S) -> [ F ]o (P s)

[_]t : forall {F G} -> F => G -> forall {X} -> [ F ]o X -> [ G ]o X
[_]t {F} {G} t (s , k) = [ G ]m k (t s)

[_]r : forall {F G} -> (forall {X} -> [ F ]o X -> [ G ]o X) -> F => G
[ f ]r s = f (s , \ p -> p)

I : Con
I = One <! \ _ -> One

_!>>_ : Con -> Con -> Con
(S <! P) !>> (S' <! P') = [ S' <! P' ]o S <! \ (s' , k) -> P' s' >< (k - P)

id : {F : Con} -> F => F
id {F} = [_]r {F}{F} \ x -> x

comp : {F G : Con}{X : Set} -> [ G ]o ([ F ]o X) -> [ F !>> G ]o X
comp (s , k) = (s , k - fst) , \ (p , p') -> snd (k p) p'

pmoc : {F G : Con}{X : Set} -> [ F !>> G ]o X -> [ G ]o ([ F ]o X)
pmoc ((s , f) , k) = s , \ p -> f p , ((p ,_) - k)

map : (F : Con){G H : Con} -> G => H -> (G !>> F) => (H !>> F)
map F {G}{H} gh = [ pmoc {G}{F} - [ F ]m [ gh ]t - comp {H}{F} ]r 

pam : {F G : Con}(H : Con) -> F => G -> (H !>> F) => (H !>> G)
pam {F}{G}H fg = [ pmoc {H}{F} - [ fg ]t - comp {H}{G} ]r

rid : {F : Con} -> F => (F !>> I)
rid {F} s = (<> , \ _ -> s) , snd

dir : {F : Con} -> (F !>> I) => F
dir (<> , s) = s <> , \ p -> <> , p

dil : {F : Con} -> (I !>> F) => F
dil (s , _) = s , (_, <>)

asso : {F G H : Con} -> ((F !>> G) !>> H) => (F !>> (G !>> H))
asso {F}{G}{H} = [ pmoc{F !>> G}{H} - [ H ]m (pmoc{F}{G})
                 - comp{G}{H} - comp{F}{G !>> H} ]r

_=>=_ : {F G H : Con} -> F => G -> G => H -> F => H
(fg =>= gh) = [ [ fg ]t - [ gh ]t ]r

here : {F : Con} -> Div F => I
here (s , h) = <> , \ _ -> h

deco : {F : Con} -> Div F => (Div F !>> Div F)
deco (s , h) = ((s , h) , (s ,_)) , snd

law1 : {F : Con} -> (deco {F} =>= (pam (Div F) (here {F}) =>= dir {Div F})) ~ id {Div F}
law1 = r~

law2 : {F : Con} -> (deco {F} =>= (map (Div F) (here {F}) =>= dil {Div F})) ~ id {Div F}
law2 = r~

law3 : {F : Con} -> (deco {F} =>= pam (Div F) (deco {F}))
                  ~ (deco {F} =>= (map (Div F) (deco {F}) =>= asso {Div F}{Div F}{Div F}))
law3 = r~

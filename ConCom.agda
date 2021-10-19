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

I : Con
I = One <! \ _ -> One

_!>>_ : Con -> Con -> Con
(S <! P) !>> (S' <! P') = [ S' <! P' ]o S <! \ (s' , k) -> P' s' >< (k - P)

id : {F : Con} -> F => F
id s = s , \ p -> p

map : (F : Con){G H : Con} -> G => H -> (G !>> F) => (H !>> F)
map F gh (s , k) = (s , k - gh - fst) , \ (p , p') -> p , snd (gh (k p)) p'

pam : {F G : Con}(H : Con) -> F => G -> (H !>> F) => (H !>> G)
pam H fg (s , k)
  = ([ fg ]t (s , k))
  , \ (p , p') -> snd (fg s) p , p'

rid : {F : Con} -> F => (F !>> I)
rid s = (<> , \ _ -> s) , snd

dir : {F : Con} -> (F !>> I) => F
dir (<> , s) = s <> , \ p -> <> , p

dil : {F : Con} -> (I !>> F) => F
dil (s , _) = s , (_, <>)

asso : {F G H : Con} -> ((F !>> G) !>> H) => (F !>> (G !>> H))
asso (s , k) = ((s , (k - fst)) , \ (p , p') -> snd (k p) p')
             , \ ((p , p') , p'') -> p , (p' , p'')


_=>=_ : {F G H : Con} -> F => G -> G => H -> F => H
(fg =>= gh) s = fst (gh (fst (fg s))) , \ p -> snd (fg s) (snd (gh (fst (fg s))) p)

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

module Pub where

open import Basics
open import Cat

record Pub[_>_]~[_>_] {S P Q R}
  (g* : S >> P)(f : P >> R)(f* : S >> Q)(g : Q >> R) : Set where
  field
    commutes : (g* ->- f) ~><~ (f* ->- g)
    universally : forall {S'}(g' : S' >> P)(f' : S' >> Q)
      -> (g' ->- f) ~><~ (f' ->- g)
      -> (S' >> S) >< \ h
      -> (g' ~><~ (h ->- g*))
       * (f' ~><~ (h ->- f*))
open Pub[_>_]~[_>_]

module _  {S P Q R}
    {g* g*' : S >> P}{f f' : P >> R}{f* f*' : S >> Q}{g g' : Q >> R}
  where
  
  pubResp[_>_]~[_>_] :
       g* ~><~ g*' -> f ~><~ f' -> f* ~><~ f*' -> g ~><~ g'
    -> Pub[ g*  > f  ]~[ f*  > g  ]
    -> Pub[ g*' > f' ]~[ f*' > g' ]
  commutes (pubResp[ g*q > fq ]~[ f*q > gq ] p) =
    (g*' ->- f') < g*q ~>~ fq !~
    (g* ->- f) ~! commutes p >
    (f* ->- g) ~! f*q ~>~ gq >
    (f*' ->- g') [==]
  universally (pubResp[ g*q > fq ]~[ f*q > gq ] p) g0 f0 q0
    with h , l0 , r0 <- universally p g0 f0 (
      (g0 ->- f) ~! (g0 [==]) ~>~ fq >
      (g0 ->- f') ~! q0 >
      (f0 ->- g') < (f0 [==]) ~>~ gq !~
      (f0 ->- g) [==])
    = h
    , (g0 ~! l0 >
       h ->- g* ~! (h [==]) ~>~ g*q >
       h ->- g*' [==])
    , (f0 ~! r0 >
       h ->- f* ~! (h [==]) ~>~ f*q >
       h ->- f*' [==])

pubId : forall {Q R}(g : Q >> R) -> Pub[ g > iA ]~[ iA > g ]
commutes (pubId g) = g [==]
universally (pubId g) g' f' q = f' , q , (f' [==])

pubCo : forall {Q R S T U V}
  {g2 : Q >> R}
  {h* : Q >> S}{h : R >> T}
  {g1 : S >> T}
  {f* : S >> U}{f : T >> V}
  {g0 : U >> V}
  -> Pub[ g2 > h ]~[ h* > g1 ]
  -> Pub[ g1 > f ]~[ f* > g0 ]
  -> Pub[ g2 > (h ->- f) ]~[ (h* ->- f*) > g0 ]
commutes (pubCo {g2 = g2} {h*} {h} {g1} {f*} {f} {g0} r s) =
  ((g2 ->- h) ->- f) ~! commutes r ~>~ (f [==]) >
  (h* ->- (g1 ->- f)) ~! (h* [==]) ~>~ commutes s >
  ((h* ->- f*) ->- g0) [==]
universally (pubCo {g2 = g2} {h*} {h} {g1} {f*} {f} {g0} r s) a b q =
  let c , u , v = universally s (a ->- h) b
        (((a ->- h) ->- f) ~! q >
         (b ->- g0) [==]) in
  let d , x , y = universally r a c u in
  d , x , (
  b ~! v >
  (c ->- f*) ~! y ~>~ (f* [==]) >
  (d ->- (h* ->- f*)) [==])

pubInj : forall {P R}{f : P >> R} -> Inj f -> Pub[ iA > f ]~[ iA > f ]
commutes (pubInj fi) = _ [==]
universally (pubInj fi) g' f' q
  = f'
  , injCo fi q
  , (_ [==])
  
pubFlip : forall {S P Q R}
  {g* : S >> P}{f : P >> R}{f* : S >> Q}{g : Q >> R}
  -> Pub[ g* > f ]~[ f* > g ]
  -> Pub[ f* > g ]~[ g* > f ]
commutes (pubFlip s) = _ < commutes s !~ _ [==]
universally (pubFlip s) f' g' q =
  let h , p , r = universally s g' f' (_ < q !~ _ [==]) in
  h , r , p

pubNo : forall {P Q R}
     {g* : `0 >> P}{f : P >> R}
     {f* : `0 >> Q}{g : Q >> R}
  -> (forall {x y} -> fo f x ~ fo g y -> Zero)
  -> Pub[ g* > f ]~[ f* > g ]
commutes (pubNo n) ()
universally (pubNo n) {`0} g' f' q = iA , (\ ()) , (\ ())
universally (pubNo n) {`1} g' f' q with () <- n (q <>)
universally (pubNo n) {`N} g' f' q with () <- n (q ze)

pubUn : forall {P Q R}{f : P >> R}{g : Q >> R} p q
  -> fo f p ~ fo g q
  -> (forall x y -> fo f x ~ fo g y -> (x ~ p) * (y ~ q))
  -> Pub[ eA p > f ]~[ eA q > g ]
commutes (pubUn p q y u) = \ _ -> y
universally (pubUn p q y u) {`0} g' f' z = _ , (\ ()) , (\ ())
universally (pubUn p q y u) {`1} g' f' z =
  let s , t = u (fo g' <>) (fo f' <>) (z <>) in
  _ , K- s , K- t
universally (pubUn p q y u) {`N} g' f' z = _
  , (\ n -> let s , t = u (fo g' n) (fo f' n) (z n) in s)
  , (\ n -> let s , t = u (fo g' n) (fo f' n) (z n) in t)

pubNa : {g* f f* g : Nat -> Nat}
  -> (forall n -> f (g* n) ~ g (f* n))
  -> (forall x y -> f x ~ g y -> Nat >< \ z -> (x ~ g* z) * (y ~ f* z))
  -> Pub[ go g* > go f ]~[ go f* > go g ]
commutes (pubNa y u) = y
universally (pubNa y u) {`0} g' f' q = nA , (\ ()) , (\ ())
universally (pubNa y u) {`1} g' f' q = 
  let n , s , t = u (fo g' <>) (fo f' <>) (q <>) in
  go (K- n) , (K- s) , (K- t)
universally (pubNa y u) {`N} g' f' q
  = (go \ n -> fst (u (fo g' n) (fo f' n) (q n)))
  , (\ n -> fst (snd (u (fo g' n) (fo f' n) (q n))))
  , (\ n -> snd (snd (u (fo g' n) (fo f' n) (q n))))

pubMo : forall {S P Q R T}
  {g* : S >> P}{f : P >> R}{f* : S >> Q}{g : Q >> R}
  -> Pub[ g* > f ]~[ f* > g ]
  -> (h : R >> T)
  -> Inj h
  -> Pub[ g* > (f ->- h) ]~[ f* > (g ->- h) ]
pubMo p h i = pubCo (pubFlip (pubCo (pubFlip p) (pubId _)))
                    (pubFlip (pubCo (pubFlip (pubId _)) (pubInj i)))

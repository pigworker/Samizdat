module TermQuad where

open import Basics
open import Cat
open import Pub
open import Quad
open import Term

module _ {s0 b0 s1 b1 : Two} where

  squareZBD : Rectifier ([_]F {va s0 b0 ff}) ([_]F {va s1 b1 ff})
  squareZBD `id g = _ , g , `id , pubId _
  squareZBD f `id = _ , `id , f , pubFlip (pubId _)
  squareZBD `no g = _ , `no , `no , pubNo \ { {()} }
  squareZBD f `no = _ , `no , `no , pubNo \ { {_} {()} }
  squareZBD `ze `ze = _ , `id , `id , pubInj (funInj {va ff ff ff} `ze)
  squareZBD `ze `su = _ , `no , `no , pubNo \ ()
  squareZBD `ze `du = _ , `id , `ze , pubUn <> ze r~ \ _ y q -> r~ , zedu y q 
  squareZBD `ze `bu = _ , `no , `no , pubNo \ ()
  squareZBD `su `ze = _ , `no , `no , pubNo \ ()
  squareZBD `su `su = _ , `id , `id , pubInj (funInj {va tt ff ff} `su)
  squareZBD `su `du = _ , `bu , `su ,
    pubNa (\ _ -> r~) \ { x ze () ; .(su- (du- y)) (su- y) r~ -> _ , r~ , r~}
  squareZBD `su `bu = _ , `du , `id ,
    pubNa (\ _ -> r~) (\ { .(du- x) x r~ -> _ , r~ , r~ })
  squareZBD `du `ze = _ , `ze , `id ,
    pubUn ze <> r~ \ x _ q -> zedu x (sym q) , r~
  squareZBD `du `su = _ , `su , `bu ,
    pubNa (\ _ -> r~) \ { ze y () ; (su- x) .(su- (du- x)) r~ -> _ , r~ , r~ }
  squareZBD `du `du = _ , `id , `id , pubInj (funInj {va ff tt ff} `du)
  squareZBD `du `bu = _ , `no , `no , pubNo \ q -> budu (sym q)
  squareZBD `bu `ze = _ , `no , `no , pubNo \ ()
  squareZBD `bu `su = _ , `id , `du ,
    pubNa (\ _ -> r~) (\ { x .(du- x) r~ -> _ , r~ , r~ })
  squareZBD `bu `du = _ , `no , `no , pubNo budu
  squareZBD `bu `bu = _ , `id , `id , pubInj (funInj {va ff tt ff} `bu)

squareF : Rectifier ([_]F {va ff ff tt}) ([_]F {va ff ff tt})
squareF `id g = _ , g , `id , pubId _
squareF f `id = _ , `id , f , pubFlip (pubId _)
squareF `no g = _ , `no , `no , pubNo \ { {()} }
squareF f `no = _ , `no , `no , pubNo \ { {_} {()} }
squareF `ze `ze = _ , `id , `id , pubInj (funInj {va ff ff ff} `ze)
squareF `ze `fu = _ , `id , `ze , pubUn _ _ r~ \ { x ze q -> r~ , r~ }
squareF `fu `ze = _ , `ze , `id , pubUn _ _ r~ \ { ze y q -> r~ , r~ }
squareF `fu `fu = _ , `id , `id , pubInj fufu

quadFZBDS : Quadrifier
  (([_]T - [_]F {va ff ff tt}) && lcomp ([_]F {va ff tt ff}))
  ([_]F {va tt tt ff})
  ([_]F {va tt tt ff})
  (([_]T - [_]F {va ff ff tt})) 
quadFZBDS `id g = _ , (g -&- nil) , `id , pubId _
quadFZBDS `no g = _ , (`no -&- nil) , `no , pubNo \ { {()} }
quadFZBDS f `no = _ , (`no -&- nil) , `no , pubNo \ { {_} {()} }
quadFZBDS `ze `ze = _ , (`id -&- nil) , `id ,
  pubUn _ _ r~ (\ _ _ _ -> r~ , r~)
quadFZBDS `ze `fu = _ , (`id -&- nil) , `ze ,
  pubUn <> ze r~ \ { x ze q -> r~ , r~ }
quadFZBDS `su `ze = _ , (`no -&- nil) , `no , pubNo \ ()
quadFZBDS `su `fu = _ , (`fu -&- one `du) , `su ,
  pubNa (_ [==]) (\ { .(du- (fu- y)) (su- y) r~ -> _ , r~ , r~ })
quadFZBDS `du `ze = _ , (`ze -&- nil) , `id ,
  pubUn ze <> r~ (\ { ze y q -> r~ , r~ })
quadFZBDS `du `fu = _ , (`ze -&- nil) , `ze ,
  pubUn ze ze r~ (\
    { ze ze q -> r~ , r~
    ; (su- x) (su- y) q -> magic (budu (natNoConf q))
    })
quadFZBDS `bu `ze = _ , (`no -&- nil) , `no , pubNo \ ()
quadFZBDS `bu `fu = _ , (`fu -&- nil) , `su ,
  pubNa (_ [==]) \ { x (su- y) q -> _ , bubu q , r~ }

splay : Rectifier
  (([_]T - [_]F {va ff ff tt}) && lcomp ([_]F {va ff tt ff}))
  ([_]F {va tt tt ff})
splay (c -&- (_ , fs)) g0
  with _ , g1 , fs1 , p1 <- qstrip squareZBD fs g0
  with _ , (c2 -&- (_ , fs2)) , g2 , p2 <- quadFZBDS g1 c
  = _ , g2 , (c2 -&- (_ , (fs2 ++ fs1)))
  , pubResp[ [ g2 ]F [==] > [ [ c ]T ]F ->- (ncomp [_]F fs) [==]
         ]~[ ([ [ c2 ]T ]F [==]) ~>~ catComp [_]F fs2 fs1 > [ g0 ]F [==] ]
         (pubCo (pubFlip p2) p1)

squareFZBD : Quadrifier ([_]T - [_]F {va ff ff tt}) ([_]F {va ff tt ff})
                      ([_]F {va tt tt ff}) ([_]T - [_]F {va ff ff tt})
squareFZBD `id g = _ , g , `id , pubId _
squareFZBD `no g = _ , `no , `no , pubNo \ { {()} }
squareFZBD f `no = _ , `no , `no , pubNo \ { {_} {()} }
squareFZBD `ze `ze = _ , `id , `id ,
  pubUn _ _ r~ (\ _ _ _ -> r~ , r~)
squareFZBD `ze `fu = _ , `id , `ze ,
  pubUn <> ze r~ \ { x ze q -> r~ , r~ }
squareFZBD `du `ze = _ , `ze , `id ,
  pubUn ze <> r~ (\ { ze y q -> r~ , r~ })
squareFZBD `du `fu = _ , `ze , `ze ,
  pubUn ze ze r~ (\
    { ze ze q -> r~ , r~
    ; (su- x) (su- y) q -> magic (budu (natNoConf q))
    })
squareFZBD `bu `ze = _ , `no , `no , pubNo \ ()
squareFZBD `bu `fu = _ , `fu , `su ,
  pubNa (_ [==]) \ { x (su- y) q -> _ , bubu q , r~ }
                      
rectFZBDS : Rectifier
  ([_]F {va ff ff tt} && lcomp ([_]F {va tt tt ff}))
  ([_]F {va ff ff tt} && lcomp ([_]F {va tt tt ff}))
rectFZBDS (c0 -&- (n , fs0)) (d0 -&- (m , gs0))
  with rect squareZBD fs0 gs0 | fullEh c0 | fullEh d0
... | _ , gs1 , fs1 , p1 | isFull | isFull
  with _ , (c2 -&- (_ , fs2)) , gs2 , p2 <- qstrip (qflip splay) gs1 (`fu -&- nil)
     | _ , (d3 -&- (_ , gs3)) , fs3 , p3 <- qstrip (qflip splay) fs1 (`fu -&- nil)
  with
  _ , gs4 , fs4 , p4 <- rect squareZBD fs2 gs3
  with _ , c5 , gs5 , p5 <- qstrip squareFZBD gs4 c2
     | _ , d6 , fs6 , p6 <- qstrip squareFZBD fs4 d3
  with _ , d7 , c7 , p7 <- squareF [ c5 ]T [ d6 ]T
  = _ , (d7 -&- (_ , (gs5 ++ gs2))) , (c7 -&- (_ , (fs6 ++ fs3)))
  , pubResp[ ([ d7 ]F ->- ncomp [_]F gs5) ->- ncomp [_]F gs2
               ~! ([ d7 ]F [==]) ~>~ catComp [_]F gs5 gs2 >
              [ d7 ]F ->- ncomp [_]F (gs5 ++ gs2) [==] 
           > (go fu-_ ->- ncomp [_]F fs0) [==]
         ]~[ ([ c7 ]F ->- ncomp [_]F fs6) ->- ncomp [_]F fs3
               ~! ([ c7 ]F [==]) ~>~ catComp [_]F fs6 fs3 >
              [ c7 ]F ->- ncomp [_]F (fs6 ++ fs3) [==] 
           > (go fu-_ ->- ncomp [_]F gs0) [==] ]
     (pubCo (pubFlip (pubCo (pubFlip p7654) p2))
            (pubFlip (pubCo (pubFlip p3) (pubFlip p1))))
  where
    p7654 : Pub[  [ d7 ]F ->- ncomp [_]F gs5 > [ [ c2 ]T ]F ->- ncomp [_]F fs2
             ]~[  [ c7 ]F ->- ncomp [_]F fs6 > [ [ d3 ]T ]F ->- ncomp [_]F gs3 ]
    p7654 = pubCo (pubFlip (pubCo (pubFlip p7) p5))
                  (pubFlip (pubCo (pubFlip p6) (pubFlip p4)))
... | _ , gs1 , fs1 , p1 | isFull | isDull d0'
  with _ , d2 , fs2 , p2 <- qstrip squareZBD fs1 d0'
  with _ , (c3 -&- (_ , fs3)) , gs3 , p3 <- qstrip (qflip splay) (([] -, f0g d2) ++ gs1) (`fu -&- nil)
  = _ , (`id -&- (_ , gs3)) , ([ c3 ]T -&- (_ , map f2g fs3 ++ fs2))
  , pubResp[ _ [==] > (go fu-_ ->- ncomp [_]F fs0) [==]
      ]~[ ([ [ c3 ]T ]F ->- ncomp [_]F fs3) ->- ncomp [_]F fs2
               ~! ([ [ c3 ]T ]F [==]) ~>~ (map-ncomp [_]F [_]F f2g f2gq fs3 ~>~ (ncomp [_]F fs2 [==]) ) >
            ([ [ c3 ]T ]F ->- ncomp [_]F (map f2g fs3)) ->- ncomp [_]F fs2
               ~! ([ [ c3 ]T ]F [==]) ~>~ catComp [_]F (map f2g fs3) fs2 >
            [ [ c3 ]T ]F ->- ncomp [_]F (map f2g fs3 ++ fs2) [==]           
      > _ [==] ]
      (pubCo (pubFlip (
        pubResp[ _ [==] >  _ < catComp [_]F ([] -, f0g d2) gs1 !~ _ [==] ]~[ _ [==] > _ [==] ] p3))
        (pubFlip (pubCo (pubFlip (pubResp[ f0gq d2 > _ [==] ]~[ _ [==] > f0gq d0' ] p2))
        (pubFlip p1))))
... | _ , gs1 , fs1 , p1 | isDull c0' | isFull
  with _ , c2 , gs2 , p2 <- qstrip squareZBD gs1 c0'
  with _ , (d3 -&- (_ , gs3)) , fs3 , p3 <- qstrip (qflip splay) (([] -, f0g c2) ++ fs1) (`fu -&- nil)
  = _ , ([ d3 ]T -&- (_ , map f2g gs3 ++ gs2)) , (`id -&- (_ , fs3))
  , pubResp[ ([ [ d3 ]T ]F ->- ncomp [_]F gs3) ->- ncomp [_]F gs2
               ~! ([ [ d3 ]T ]F [==]) ~>~ (map-ncomp [_]F [_]F f2g f2gq gs3 ~>~ (ncomp [_]F gs2 [==]) ) >
            ([ [ d3 ]T ]F ->- ncomp [_]F (map f2g gs3)) ->- ncomp [_]F gs2
               ~! ([ [ d3 ]T ]F [==]) ~>~ catComp [_]F (map f2g gs3) gs2 >
            [ [ d3 ]T ]F ->- ncomp [_]F (map f2g gs3 ++ gs2) [==] > _ [==]
            ]~[ _ [==] > (go fu-_ ->- ncomp [_]F gs0) [==] ]
    (pubFlip (pubCo (pubFlip (pubResp[ _ [==] > _ < catComp [_]F ([] -, f0g c2) fs1 !~ _ [==] ]~[
          _ [==] > _ [==] ] p3))
      (pubFlip (pubCo (pubFlip
        (pubResp[ f0gq c2 > _ [==] ]~[ _ [==] > f0gq c0' ] p2))
        p1))))
... | _ , gs1 , fs1 , p1 | isDull c0' | isDull d0'
  with _ , c2 , gs2 , p2 <- qstrip squareZBD gs1 c0'
     | _ , d3 , fs3 , p3 <- qstrip squareZBD fs1 d0'
  with _ , d4 , c4 , p4 <- squareZBD c2 d3
  = _ , (f0g d4 -&- (_ , gs2)) , (f0g c4 -&- (_ , fs3))
  , pubCo (pubFlip (pubCo (pubFlip (pubResp[ f0gq d4 > _ [==] ]~[ f0gq c4 > _ [==] ] p4))
                    (pubResp[ _ [==] > _ [==] ]~[ _ [==] > f0gq c0' ] p2)))
    (pubFlip (pubCo (pubFlip (pubResp[ _ [==] > _ [==] ]~[ _ [==] > f0gq d0' ] p3))
                    (pubFlip p1)))

chunk : forall {S T} -> Fun (va tt tt tt) S T -> (Fun (va ff ff tt) & _-[ Fun (va tt tt ff) ]-_) S T
chunk `id = `id -&- nil
chunk `no = `id -&- one `no
chunk `ze = `id -&- one `ze
chunk `su = `id -&- one `su
chunk `du = `id -&- one `du
chunk `bu = `id -&- one `bu
chunk `fu = `fu -&- nil

chunkq : {S T : Obj} (a : Fun (va tt tt tt) S T) ->
      [ a ]F ~><~ ([_]F && lcomp [_]F) (chunk a)
chunkq `id = _ [==]
chunkq `no = _ [==]
chunkq `ze = _ [==]
chunkq `su = _ [==]
chunkq `du = _ [==]
chunkq `bu = _ [==]
chunkq `fu = _ [==]

smooth : forall {n S T}
  -> S -[ Fun (va ff ff tt) & _-[  Fun (va tt tt ff) ]-_ / n ]- T
  -> S -[ Fun (va tt tt tt) ]- T
smooth [] = nil
smooth (fss -, (f -&- (_ , fs))) =
  let _ , gs = smooth fss in _ , ((gs -, f1g f) ++ map f6g fs )

smoothq : forall {n S T}
      (gs* : S -[ Fun (va ff ff tt) & _-[  Fun (va tt tt ff) ]-_ / n ]- T) ->
      ncomp ([_]F && lcomp [_]F) gs* ~><~
      lcomp [_]F (smooth gs*)
smoothq [] = _ [==]
smoothq (gs* -, (f -&- (_ , fs))) = 
  (ncomp ([_]F && lcomp [_]F) gs* ->- ([_]F && lcomp [_]F) (f -&- (_ , fs)))
      ~! smoothq gs* ~>~ ((([ f ]F) ->- ncomp [_]F fs) [==]) >
  ((lcomp [_]F (smooth gs*) ->- [ f ]F) ->- ncomp [_]F fs)
      ~! ((lcomp [_]F (smooth gs*) [==]) ~>~ f1gq f) ~>~ map-ncomp [_]F [_]F f6g f6gq fs >
  ncomp [_]F ((snd (smooth gs*) -, f1g f)) ->- ncomp [_]F (map f6g fs)
      ~! catComp [_]F _ (map f6g fs) >
  ncomp [_]F ((snd (smooth gs*) -, f1g f) ++ map f6g fs) [==]

snocWithQ : forall {R S T}(fs : R -[ Fun (va tt tt tt) ]- S)(f : Fun (va tt tt tt) S T)
  -> (R -[ Fun (va tt tt tt) ]- T) >< \ gs ->
     (lcomp [_]F fs ->- [ f ]F) ~><~ lcomp [_]F gs
snocWithQ {`0} fs f = one `no , \ ()
snocWithQ {R} fs `id = fs , (_ [==])
snocWithQ {`1} (_ , ([] -, `ze)) `su = (_ , ([] -, `ze -, `bu)) , (_ [==])
snocWithQ {`1} (_ , ([] -, `ze))`du = one `ze , (_ [==])
snocWithQ {`1} (_ , ([] -, `ze)) `fu = one `ze , (_ [==])
snocWithQ {R} (_ , (fs -, `du)) `su = snocWithQ (_ , fs) `bu
snocWithQ {R} (_ , (fs -, `bu)) `su = let (_ , gs) , q = snocWithQ (_ , fs) `su in
  (_ , (gs -, `du)) , (q ~>~ (go du-_ [==]))
snocWithQ {R} (_ , (fs -, `fu)) `bu = let (_ , gs) , q = snocWithQ (_ , fs) `su in
  (_ , (gs -, `fu)) , (q ~>~ (go fu-_ [==]))
snocWithQ (_ , fs) f = (_ , (fs -, f)) , (_ [==])

snoc : forall {R S T} -> R -[ Fun (va tt tt tt) ]- S -> Fun (va tt tt tt) S T
                      -> R               -[ Fun (va tt tt tt) ]-            T
snoc {R} fs f = fst (snocWithQ fs f)


snocq : forall {R S T}(fs : R -[ Fun (va tt tt tt) ]- S)(f : Fun (va tt tt tt) S T)
  -> (lcomp [_]F fs ->- [ f ]F) ~><~ lcomp [_]F (snoc fs f)
snocq fs f = snd (snocWithQ fs f)

norm : forall {S T} -> S -[ Fun (va tt tt tt) ]- T -> S -[ Fun (va tt tt tt) ]- T
norm (_ , []) = nil
norm (_ , (fs -, f)) = snoc (norm (_ , fs)) f

normq : forall {S T}(fs : S -[ Fun (va tt tt tt) ]- T) ->
  lcomp [_]F fs ~><~ lcomp [_]F (norm fs)
normq (_ , []) = _ [==]
normq (_ , (fs -, f)) = 
  (lcomp [_]F (_ , fs) ->- [ f ]F) ~! normq (_ , fs) ~>~ ([ f ]F [==]) >
  (lcomp [_]F (norm (_ , fs)) ->- [ f ]F) ~! snocq (norm (_ , fs)) f >
  lcomp [_]F (snoc (norm (_ , fs)) f) [==]

unify : Rectifier (lcomp ([_]F {va tt tt tt})) (lcomp ([_]F {va tt tt tt}))
unify (_ , fs) (_ , gs)
  with _ , gs* , fs* , p <- rect rectFZBDS (map chunk fs) (map chunk gs)
  = _ , norm (smooth gs*) , norm (smooth fs*) , 
    pubResp[ ncomp ([_]F && lcomp [_]F) gs* ~! smoothq gs* >
              lcomp [_]F (smooth gs*) ~! normq (smooth gs*) >
              lcomp [_]F (norm (smooth gs*)) [==]
           > _ < map-ncomp [_]F ([_]F && lcomp [_]F) chunk chunkq fs !~ _ [==]
         ]~[ ncomp ([_]F && lcomp [_]F) fs* ~! smoothq fs* >
              lcomp [_]F (smooth fs*) ~! normq (smooth fs*) >
              lcomp [_]F (norm (smooth fs*)) [==]
           > _ < map-ncomp [_]F ([_]F && lcomp [_]F) chunk chunkq gs !~ _ [==]
           ] p

test0 = unify (_ , ([] -, `fu)) (_ , ([] -, `fu -, `su -, `su))
test1 = unify (_ , ([] -, `fu)) (_ , ([] -, `fu -, `fu))

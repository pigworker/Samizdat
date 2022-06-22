module Thin where

open import Basics
open import Bwd
open import SmolCat

module _ {X : Set} where

  infix 40 _<=_
  infixl 50 _-^_ _-^,_
  data _<=_ : Bwd X -> Bwd X -> Set where
    _-^_ : forall {ga de : Bwd X} -> ga <= de -> forall y -> ga      <= de -, y
    _-,_ : forall {ga de : Bwd X} -> ga <= de -> forall x -> ga -, x <= de -, x
    [] : [] <= []

  infix 40 [_<&_]~_
  data [_<&_]~_ : forall {ga de xi} -> ga <= de -> de <= xi -> ga <= xi -> Set where
    _-^_ : forall {ga de xi}{th : ga <= de}{ph : de <= xi}{ps : ga <= xi}
        -> [ th <& ph ]~ ps -> forall x
        -> [ th <& ph -^ x ]~ ps -^ x
    _-^,_ : forall {ga de xi}{th : ga <= de}{ph : de <= xi}{ps : ga <= xi}
        -> [ th <& ph ]~ ps -> forall x
        -> [ th -^ x <& ph -, x ]~ ps -^ x
    _-,_ : forall {ga de xi}{th : ga <= de}{ph : de <= xi}{ps : ga <= xi}
        -> [ th <& ph ]~ ps -> forall x
        -> [ th -, x <& ph -, x ]~ ps -, x
    [] : [ [] <& [] ]~ []

  inj : forall {ga de xi}{ph : de <= xi}{ps : ga <= xi}
          (p q : < [_<& ph ]~ ps >) -> p ~ q
  inj (! v -^ x) (! w -^ .x) with r~ <- inj (! v) (! w) = r~
  inj (! v -^, x) (! w -^, .x) with r~ <- inj (! v) (! w) = r~
  inj (! (v -, x)) (! (w -, .x)) with r~ <- inj (! v) (! w) = r~
  inj (! []) (! []) = r~

  open Cat
  THIN : Cat _<=_
  iden THIN {[]} = []
  iden THIN {ga -, x} = iden THIN {ga} -, x
  [_&_]~_ THIN = [_<&_]~_
  tri THIN th (ph -^ y)         = let ! v = tri THIN th ph in ! v -^ y 
  tri THIN (th -^ .x) (ph -, x) = let ! v = tri THIN th ph in ! v -^, x
  tri THIN (th -, .x) (ph -, x) = let ! v = tri THIN th ph in ! v -, x
  tri THIN     []         []    =                             ! []
  triq THIN (! v -^  x) (! w -^  .x) with r~ <- triq THIN (! v) (! w) = r~
  triq THIN (! v -^, x) (! w -^, .x) with r~ <- triq THIN (! v) (! w) = r~
  triq THIN (! v -,  x) (! w -,  .x) with r~ <- triq THIN (! v) (! w) = r~
  triq THIN (!   []   ) (!   []    ) = r~
  idTri THIN (th -^ y) = idTri THIN th -^ y
  idTri THIN (th -, x) = idTri THIN th -, x
  idTri THIN     []    =               []
  triId THIN (th -^ y) = triId THIN th -^, y
  triId THIN (th -, x) = triId THIN th -, x
  triId THIN     []    =               []
  ass03 THIN (v        ^ w -^ x ) with v' ^ w' <- ass03 THIN (v ^ w) = v' -^ x  ^ w' -^ x
  ass03 THIN (v -^ .x  ^ w -^, x) with v' ^ w' <- ass03 THIN (v ^ w) = v' -^ x  ^ w' -^, x
  ass03 THIN (v -^, .x ^ w -, x ) with v' ^ w' <- ass03 THIN (v ^ w) = v' -^, x ^ w' -^, x
  ass03 THIN (v -, .x  ^ w -, x ) with v' ^ w' <- ass03 THIN (v ^ w) = v' -, x  ^ w' -, x
  ass03 THIN (  []     ^   []   )                                    =    []    ^    []

  infix 45 _/u\_
  infixl 50 _-,^_
  data _/u\_ : forall {ga}
               {ga0}(th0 : ga0 <= ga)
               {ga1}(th1 : ga1 <= ga)
               -> Set where
    _-^,_ : forall {ga}
                  {ga0}{th0 : ga0 <= ga}
                  {ga1}{th1 : ga1 <= ga}
               -> th0 /u\ th1 -> forall x
               -> th0 -^ x /u\ th1 -, x
    _-,^_ : forall {ga}
                  {ga0}{th0 : ga0 <= ga}
                  {ga1}{th1 : ga1 <= ga}
               -> th0 /u\ th1 -> forall x
               -> th0 -, x /u\ th1 -^ x
    _-,_ : forall {ga}
                  {ga0}{th0 : ga0 <= ga}
                  {ga1}{th1 : ga1 <= ga}
               -> th0 /u\ th1 -> forall x
               -> th0 -, x /u\ th1 -, x
    [] : [] /u\ []

  cop : forall {ga}
               {ga0}(ph0 : ga0 <= ga)
               {ga1}(ph1 : ga1 <= ga) ->
        (< ga0 <=_ *: ga1 <=_ >) >< \ (th0 ^ th1) ->
        th0 /u\ th1 * (< [ th0 <&_]~ ph0 *: [ th1 <&_]~ ph1 >)
  cop (ph0 -^ y) (ph1 -^ .y) =
    let ! u , v ^ w = cop ph0 ph1 in ! u , v -^ y ^ w -^ y
  cop (ph0 -^ y) (ph1 -, .y) =
    let ! u , v ^ w = cop ph0 ph1 in ! u -^, y , v -^, y ^ w -, y
  cop (ph0 -, x) (ph1 -^ .x) =
    let ! u , v ^ w = cop ph0 ph1 in ! u -,^ x , v -, x ^ w -^, x
  cop (ph0 -, x) (ph1 -, .x) =
    let ! u , v ^ w = cop ph0 ph1 in ! u -, x , v -, x ^ w -, x
  cop [] [] = ! [] , [] ^ []

  copU : forall {ga}
               {ga0}{ph0 : ga0 <= ga}
               {ga1}{ph1 : ga1 <= ga} ->
      {(th0 ^ th1) : < ga0 <=_ *: ga1 <=_ >} ->
      th0 /u\ th1 ->
      ((th , _) : < [ th0 <&_]~ ph0 *: [ th1 <&_]~ ph1 >) ->
      {(ps0 ^ ps1) : < ga0 <=_ *: ga1 <=_ >} ->
      ((ps , _) : < [ ps0 <&_]~ ph0 *: [ ps1 <&_]~ ph1 >) ->
      < [ th0 <&_]~ ps0 *: [_<& ps ]~ th *: [ th1 <&_]~ ps1 >
  copU u (v -^ _ ^ w -^ _)   (x -^ _ ^ y -^ _)
    = let ! a , b , c = copU u (v ^ w) (x ^ y) in ! a , b -^ _ , c
  copU u (v -^ _ ^ w -^ _)   (x -^, _ ^ y -^, _)
    = let ! a , b , c = copU u (v ^ w) (x ^ y) in ! a -^ _ , b -^, _ , c -^ _
  copU (u -^, _) (v -^, _ ^ w -, _) (x -^, _ ^ y -, _)
    = let ! a , b , c = copU u (v ^ w) (x ^ y) in ! a -^, _ , b -, _ , c -, _
  copU (u -,^ _) (v -, _ ^ w -^, _) (x -, _ ^ y -^, _)
    = let ! a , b , c = copU u (v ^ w) (x ^ y) in ! a -, _ , b -, _ , c -^, _
  copU (u -, _)  (v -, _ ^ w -, _) (x -, _ ^ y -, _)
    = let ! a , b , c = copU u (v ^ w) (x ^ y) in ! a -, _ , b -, _ , c -, _
  copU u ([] ^ []) ([] ^ []) = ! [] , [] , []

  data Pub : forall {de ga}{(th0 ^ ph0) (th1 ^ ph1) : < de <=_ *: _<= ga >}
             -> < [ th0 <& ph0 ]~_ *: [ th1 <& ph1 ]~_ > -> Set where
    _-^_ : forall {de ga}{(th0 ^ ph0) (th1 ^ ph1) : < de <=_ *: _<= ga >}
             {(v ^ w) : < [ th0 <& ph0 ]~_ *: [ th1 <& ph1 ]~_ >} ->
             Pub (v ^ w) -> forall x -> Pub (v -^ x ^ w -^ x)
    _-^,_ : forall {de ga}{(th0 ^ ph0) (th1 ^ ph1) : < de <=_ *: _<= ga >}
             {(v ^ w) : < [ th0 <& ph0 ]~_ *: [ th1 <& ph1 ]~_ >} ->
             Pub (v ^ w) -> forall x -> Pub (v -^ x ^ w -^, x)
    _-,^_ : forall {de ga}{(th0 ^ ph0) (th1 ^ ph1) : < de <=_ *: _<= ga >}
             {(v ^ w) : < [ th0 <& ph0 ]~_ *: [ th1 <& ph1 ]~_ >} ->
             Pub (v ^ w) -> forall x -> Pub (v -^, x ^ w -^ x)
    _-,_ : forall {de ga}{(th0 ^ ph0) (th1 ^ ph1) : < de <=_ *: _<= ga >}
             {(v ^ w) : < [ th0 <& ph0 ]~_ *: [ th1 <& ph1 ]~_ >} ->
             Pub (v ^ w) -> forall x -> Pub (v -, x ^ w -, x)
    [] : Pub ([] ^ [])

  pub : forall {ga0 ga1 ga}(ph0 : ga0 <= ga)(ph1 : ga1 <= ga) ->
    < _<= ga0 *: _<= ga1 > >< \ (th0 ^ th1) ->
    < [ th0 <& ph0 ]~_ *: [ th1 <& ph1 ]~_ > >< Pub
  pub (ph0 -^ y) (ph1 -^ .y) = let ! ! p = pub ph0 ph1 in ! ! p -^ y
  pub (ph0 -^ y) (ph1 -, .y) = let ! ! p = pub ph0 ph1 in ! ! p -^, y
  pub (ph0 -, x) (ph1 -^ .x) = let ! ! p = pub ph0 ph1 in ! ! p -,^ x
  pub (ph0 -, x) (ph1 -, .x) = let ! ! p = pub ph0 ph1 in ! ! p -, x
  pub [] [] = ! ! []

  pubU : forall {de ga}{(th0 ^ ph0) (th1 ^ ph1) : < de <=_ *: _<= ga >}
         -> {p@(th , _) : < [ th0 <& ph0 ]~_ *: [ th1 <& ph1 ]~_ >}
         -> Pub p
         -> forall {(ps0 ^ ps1) : < _<= _ *: _<= _ >}
         -> ((ps , _) : < [ ps0 <& ph0 ]~_ *: [ ps1 <& ph1 ]~_ >)
         -> < [_<& th0 ]~ ps0 *: [_<& th ]~ ps *: [_<& th1 ]~ ps1 >
  pubU (p -^ _) (x -^ _ ^ y -^ _) =
    let ! a , b , c = pubU p (x ^ y) in ! a , b -^ _ , c
  pubU (p -^, _) (x -^ _ ^ y -^, _) =
    let ! a , b , c = pubU p (x ^ y) in ! a , b -^ _ , c -^ _
  pubU (p -,^ _) (x -^, _ ^ y -^ _) =
    let ! a , b , c = pubU p (x ^ y) in ! a -^ _ , b -^ _ , c
  pubU (p -, _) (x -^, _ ^ y -^, _) =
    let ! a , b , c = pubU p (x ^ y) in ! a -^, _ , b -^, _ , c -^, _
  pubU (p -, _) (x -, _ ^ y -, _) =
    let ! a , b , c = pubU p (x ^ y) in ! a -, _ , b -, _ , c -, _
  pubU [] ([] ^ []) = ! [] , [] , []

  module _ (ga : Bwd X) where
                   
    UNION : Products ((THIN ^op) \\ ga)
    UNION (! ph0) (! ph1) = let ! u , v ^ w = cop ph0 ph1 in record
      { best = record
        { limArr = \ { ff -> ! v ; tt -> ! w }
        ; limTri = \ { {ff} r~ -> idTri THIN _ ; {tt} r~ -> idTri THIN _ }
        }
      ; factor = \ c -> 
          let ps , a , b , c =
               copU u (v ^ w) (snd (limArr c ff) ^ snd (limArr c tt))
          in (ps , b) , (\ { ff -> a ; tt -> c })
             , \ z _ -> inj z (! b)
      }

    INTERSECTION : Products (THIN // ga)
    INTERSECTION (! ph0) (! ph1) = let ! (v ^ w) , p = pub ph0 ph1 in record
      { best = record
        { limArr = \ { ff -> ! v ; tt -> ! w }
        ; limTri = \ { {ff} r~ -> triId THIN _ ; {tt} r~ -> triId THIN _ }
        }
      ; factor = \ c ->
          let ps , a , b , c = pubU p (snd (limArr c ff) ^ snd (limArr c tt))
          in  (ps , b) , (\ { ff -> a ; tt -> c }) , \ z _ -> inj z (! b)
      }

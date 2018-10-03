------------------------------------------------------------------------------
-----                                                                    -----
-----     Dag: directed acyclic graphs                                   -----
-----                                                                    -----
------------------------------------------------------------------------------

module Dag where

import Data.Maybe
import Data.Monoid

import BigArray

newtype Dag n = Dag
  { upSets :: Arr n (Set n) -- map each node to its upward closure
  } deriving Show

upSet  :: Ord n => Dag n -> n -> Set n
upSet (Dag dag) n = fromMaybe (singleton n) (findArr n dag)

downSet :: Ord n => Dag n -> n -> Set n
downSet (Dag dag) n = singleton n <>
  foldMapArr (\ (x, xup) -> if inSet n xup then singleton x else mempty) dag

invertDag :: Ord n => Dag n -> Dag n
invertDag (Dag dag) =
  Dag (foldMapArr (\ (x, _) -> single (x, downSet (Dag dag) x)) dag)

rawDelete :: Ord n => Set n -> Dag n -> Dag n
rawDelete ns (Dag dag) = Dag $
  foldMapArr (\ (x, xup) -> if inSet x ns then mempty else
      single (x,
        foldMapArr (\ (y, ()) -> if inSet y ns then mempty else singleton y)
          xup))
    dag

edge :: Ord n => (n {-x-}, n {-y-}) -> Dag n ->
  ( Set n -- the set of nodes thus identified with y and deleted
  , Dag n -- the updated dag
  )
edge (x, y) (Dag dag) = case findArr y dag of
  Nothing -> -- y does not exist, so
    let dag' = dag <> single (x, singleton x) <> single (y, singleton y)
          -- ensure that x and y both exist, then...
    in  (mempty,
         Dag $ dag' <>
          foldMapArr
          (\ (z, zup) -> if inSet x zup then single (z, singleton y) else mempty)
          dag'  -- ...add y to every upSet containing x
        )
  Just yup  -- y exists, with upSet yup
    | inSet x yup ->  -- x is above y, so some collapse is needed
      let yis = deleteArr y (intersectSet yup (downSet (Dag dag) x))
            -- everything above y and below x, apart from y
      in  (yis, rawDelete yis (Dag dag))
    | otherwise ->
      let dag' = dag <> single (x, singleton x) -- ensure that x exists
      in  ( mempty
          , Dag (dag' <>
                 foldMapArr (\ (z, zup) -> if inSet x zup then (single (z, yup)) else mempty)
                 dag')  -- everything with x in its upSet gets yup in its upSet, too
          )

upDelete :: Ord n => n -> Dag n -> (Set n, Dag n)
upDelete n (Dag dag) = case findArr n dag of
  Nothing -> (singleton n, Dag dag)
  Just nup -> (nup, rawDelete nup (Dag dag))

downDelete :: Ord n => n -> Dag n -> (Set n, Dag n)
downDelete n dag =
  let ndn = downSet dag n
  in  (ndn, rawDelete ndn dag)

data DagComponents n = DagComponents
  { nextComponent   :: Integer              -- larger than any mentioned
  , knownComponents :: Arr Integer (Set n)  -- which things are in a component
  , whichComponent  :: Arr n Integer        -- which component a thing is in
  } deriving Show

growComponents :: Ord n => Set n -> DagComponents n -> DagComponents n
growComponents xs (DagComponents n k w) =
  case foldMapSet (\ x -> maybe [] (:[]) (findArr x w)) xs of
    [] -> DagComponents
      { nextComponent = n + 1
      , knownComponents = insertArr (n, xs) k
      , whichComponent = appEndo
          (foldMapSet (\ x -> Endo $ insertArr (x, n)) xs) w
      }
    [i] -> DagComponents
      { nextComponent = n
      , knownComponents = k <> single (i, xs)
      , whichComponent = appEndo
          (foldMapSet (\ x -> Endo $ insertArr (x, i)) xs) w
      }
    i : js ->
      let blob = xs <> foldMap (\ j -> fromMaybe mempty (findArr j k)) js
          k' = foldr deleteArr k js
      in  DagComponents
            { nextComponent = n
            , knownComponents = insertArr (i, blob) k'
            , whichComponent = appEndo
                (foldMapSet (\ x -> Endo $ insertArr (x, i)) blob) w
            }

dagComponents :: Ord n => Dag n -> DagComponents n
dagComponents (Dag dag) =
  appEndo (foldMapArr (Endo . growComponents . snd) dag)
  (DagComponents 0 emptyArr emptyArr)

dagClosure :: Ord n => n -> Dag n -> Set n
dagClosure n dag = case findArr n w of
    Just c -> case findArr c k of
      Just s -> s
  where
    DagComponents {knownComponents = k, whichComponent = w} =
      dagComponents dag

          
module CompLam where

import Control.Monad.State

import BigArray

data Inst
  = Push Int | PushReg | Restack | Swap | Pop
  | Cons | Decons
  | Load Int | Add
  deriving Show

data Exit = Jump Int | Return
  deriving Show

type Block = ([Inst], Exit)

type Heap v = (Int, Arr Int v)

type Prog = Heap Block
type Store = Heap (Int, Int)

alloc :: v -> State (Heap v) Int
alloc v = do
  (n, vs) <- get
  put (n + 1, insertArr (n, v) vs)
  return n

hunt :: Int -> State (Heap v) v
hunt i = do
  (n, vs) <- get
  let Just v = findArr i vs
  return v

type Config =
  ( Int -- register
  , [Int] -- stack
  , Store
  )

inst :: Config -> Inst -> Config
inst (r, s, m)     (Push i) = (r, i : s, m)
inst (r, s, m)      PushReg = (r, r : s, m)
inst (r, h : s, m)  Restack = (h, r : s, m)
inst (r, x : y : s, m) Swap = (r, y : x : s, m)
inst (r, _ : s, m)      Pop = (r, s, m)
inst (r, x : s, m)     Cons = (r', s, m') where
  (r', m') = runState (alloc (x, r)) m
inst (r, s, m)       Decons = (r', x : s, m) where
  (x, r') = evalState (hunt r) m
inst (_, s, m)     (Load n) = (n, s, m)
inst (x, y : s, m)  Add = (x + y, s, m)

run :: Prog -> Exit -> Config -> (Int, Store)
run p Return (r, [], m) = (r, m)
run p Return (r, i : s, m) = run p (Jump i) (r, s, m)
run p (Jump i) c = run p e (foldl inst c is) where
  (is, e) = evalState (hunt i) p

data Tm
  = V Int
  | L Tm
  | Tm :$ Tm
  | N Int
  | Tm :+ Tm
  deriving Show

compile :: [Inst]   -- prefix
        -> Tm       -- code
        -> Int      -- exit point
        -> State Prog Int
compile is (L t) k = do
  ret <- alloc ([], Return)
  bod <- compile [] t ret
  alloc (is ++ [Push bod, Cons], Jump k)
compile is (V i) k =
  alloc (is ++ concat (replicate i [Decons, Pop]) ++ [Decons, Restack, Pop], Jump k)
compile is (f :$ s) k = do
  fin <- alloc ([Decons, Swap, Cons, Push k, Swap], Return)
  fun <- compile [Restack] f fin
  compile (is ++ [PushReg]) s fun
compile is (N n) k = alloc (is ++ [Load n], Jump k)
compile is (s :+ t) k = do
  add <- alloc ([Add], Jump k)
  s' <- compile [Restack] s add
  compile (is ++ [PushReg]) t s'

topLevel :: Tm -> (Int, Prog)
topLevel t = runState p (0, emptyArr)
  where
    p = do
      ret <- alloc ([], Return)
      compile [] t ret

try :: Tm -> (Int, Store)
try t = run p (Jump e) (negate 1, [], (0, emptyArr)) where
  (e, p) = topLevel t

---

cze :: Tm
cze = L (L (V 0))

csu :: Tm
csu = L (L (L (V 1 :$ ((V 2 :$ V 1) :$ V 0))))

c2 :: Tm
c2 = csu :$ (csu :$ cze)

nsu :: Tm
nsu = L (N 1 :+ V 0)


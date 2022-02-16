module HW1.T3
  ( Tree (..)
  , tsize
  , tdepth
  , tmember
  , tinsert
  , tFromList
  ) where

-- | SBTree
data Tree a
  = Leaf
  | Branch Int (Tree a) a (Tree a)
  deriving (Show)

{-
instance Show a => Show (Tree a) where
  show Leaf = "null"
  show (Branch _ l x r) = "{\"v\":" ++ show x ++ ",\"left\":" ++ show l ++ ",\"right\":" ++ show r ++ "}"
-}

mkBranch :: Tree a -> a -> Tree a -> Tree a
mkBranch l x r = Branch (1 + tsize l + tsize r) l x r

tsize :: Tree a -> Int
tsize Leaf             = 0
tsize (Branch a _ _ _) = a

tlsize :: Tree a -> Int
tlsize Leaf             = 0
tlsize (Branch _ l _ _) = tsize l

trsize :: Tree a -> Int
trsize Leaf             = 0
trsize (Branch _ _ _ r) = tsize r

-- | Depth of the tree, O(log n).
tdepth :: Tree a -> Int
tdepth Leaf             = 0
tdepth (Branch _ l _ r) =  1 + (tdepth l `max` tdepth r)

rightRotate (Branch _ (Branch _ a p b) q c) =
  mkBranch a p $ mkBranch b q c
rightRotate x = x
leftRotate (Branch _ a p (Branch _ b q c)) =
  mkBranch (mkBranch a p b) q c
leftRotate x = x

-- | Check if the element is in the tree, O(log n)
tmember :: Ord a => a -> Tree a -> Bool
tmember _ Leaf = False
tmember a (Branch _ l k r) =
  case a `compare` k of
    LT -> tmember a l
    EQ -> True
    GT -> tmember a r

-- | Insert an element into the tree, O(log n)
tinsert :: Ord a => a -> Tree a -> Tree a
tinsert a Leaf = Branch 1 Leaf a Leaf
tinsert a was@(Branch _ l x r) =
  case a `compare` x of
    EQ -> was
    LT -> remake (tinsert a l) r
    GT -> remake l (tinsert a r)
  where
    remake l r = rebalance $ mkBranch l x r


rebalance :: Tree a -> Tree a
rebalance Leaf = Leaf
rebalance was@(Branch _ l x r) =
  let ls = tsize l in
  let rs = tsize r in
  if ls < tlsize r then
    let Branch _ nl nx nr = leftRotate $ mkBranch l x (rightRotate r) in
    rebalance $ mkBranch (rebalance nl) nx (rebalance nr)
  else if ls < trsize r then
    let Branch _ nl nx nr = leftRotate was in
    rebalance $ mkBranch (rebalance nl) nx nr
  else if rs < trsize l then
    let Branch _ nl nx nr = rightRotate $ mkBranch (leftRotate l) x r in
    rebalance $ mkBranch (rebalance nl) nx (rebalance nr)
  else if rs < tlsize l then
    let Branch _ nl nx nr = rightRotate was in
    rebalance $ mkBranch nl nx (rebalance nr)
  else
    was

-- | Build a tree from a list, O(n log n)
tFromList :: Ord a => [a] -> Tree a
tFromList = foldr tinsert Leaf

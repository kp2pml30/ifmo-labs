{-# LANGUAGE BangPatterns #-}

import Control.Monad.State
import qualified Data.Set as Set
import qualified Data.MultiMap as MMap

data L = L !Int !Int !Int !Int deriving (Eq, Ord)

instance Show L where
  show (L p q a b) = "[P" ++ show p ++ ",Q" ++ show q ++ "," ++ show a ++ "," ++ show b ++ "]"

data Line = Line L L deriving (Eq)

instance Show Line where
  show (Line f t) = show f ++ " -> " ++ show t

data MState = MState { visited :: Set.Set L, answer :: [Line]}

advanceP (L 1 q a b) = L 2 q 1 b
advanceP (L 2 q a 1) = L 2 q a 1
advanceP (L 2 q a 0) = L 3 q a 0
advanceP (L 3 q a b) = L 4 q a b
advanceP (L 4 q a b) = L 1 q 0 b

advanceQ (L p 1 a b) = L p 2 a 1
advanceQ (L p 2 0 b) = L p 4 0 b
advanceQ (L p 2 1 b) = L p 3 1 b
advanceQ (L p 3 a b) = L p 1 a 0
advanceQ (L p 4 a b) = L p 4 a b

allStates = [L p q a b | p <- [1..4], q <- [1..4], a <- [0, 1], b <- [0, 1]]
allTransitions = MMap.fromList $ concat [[(l, advanceP l), (l, advanceQ l)] | l <- allStates]

step :: L -> L -> State MState ()
step !from !cur = do
  was <- gets $ Set.member cur . visited
  modify (\st -> MState (Set.insert cur $ visited st) (Line from cur : answer st))
  if was
  then return ()
  else mapM_ (step cur) (allTransitions MMap.! cur)

main = do
  let res = execState (step (L 0 0 0 0) (L 1 1 0 0)) (MState Set.empty [])
  putStrLn "Prokopenko Kirill"
  putStrLn "# check solution.hs"
  mapM_ print (reverse $ answer res)
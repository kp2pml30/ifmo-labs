{-# LANGUAGE BlockArguments #-}

module HW1.T4
  ( tfoldr
  ) where

import HW1.T3

tfoldr :: (a -> b -> b) -> b -> Tree a -> b
tfoldr _ z Leaf = z
tfoldr f z (Branch _ l x r) =
  let resl = tfoldr f z r in
  tfoldr f (f x resl) l

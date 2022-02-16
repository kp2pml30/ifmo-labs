module HW1.T6
  ( mcat
  , epart
  ) where

import Data.Foldable
import Data.Maybe
import Data.Monoid

mcat :: Monoid a => [Maybe a] -> a
mcat = foldMap fold

epart :: (Monoid a, Monoid b) => [Either a b] -> (a, b)
epart l = (foldMap (fold . either Right Left) l, foldMap fold l)

{-# LANGUAGE BlockArguments #-}

module HW0.T4 where

import Data.Function (fix)
import Numeric.Natural

repeat' :: a -> [a]
repeat' x = fix (x:)

map' :: (a -> b) -> [a] -> [b]  -- behaves like Data.List.map
map' f =
  fix \r lst ->
    case lst of
      []    -> []
      (h:t) -> (f h):(r t)

fib :: Natural -> Natural       -- computes the n-th Fibonacci number
fib =
  fix
    (\f a b n ->
      if n == 0
      then a
      else f b (a + b) (n - 1))
    0 1

fac :: Natural -> Natural       -- computes the factorial
fac = fix (\f a n -> if n == 0 then a else f (a * n) (n - 1)) 1

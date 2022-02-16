module HW0.T3 (s, k, i, compose, contract, permute) where

import Prelude ()

s :: (a -> b -> c) -> (a -> b) -> (a -> c)
s f g x = f x (g x)

k :: a -> b -> a
k x y = x

t = k
f = s k

i :: a -> a
i = f k


-- S (K S) = λg x g1 x1. g x x1 (g1 x1)
-- S (K S) K = λx g1 x1. x (g1 x1)

compose :: (b -> c) -> (a -> b) -> (a -> c)
compose = s (k s) k

-- permute s = λx y x1.y x1(x x1)

contract :: (a -> a -> b) -> (a -> b)
contract = permute s i

{--

\fxy.fyx
\fx. s f (k x)
\f. s (k (s f)) k
s (\f. s (k (s f))) (k k)
  \f. s (k (s f))
  s (k s) (\f. k (s f))
    \f. k (s f)
    s (k k) (\f. s f)
      \f. s f
      s (k s) i
    s (k k) (s (k s) i)
  s (k s) (s (k k) (s (k s) i))
s (s (k s) (s (k k) (s (k s) i))) (k k)

 --}

permute :: (a -> b -> c) -> (b -> a -> c)
permute =  s (s (k s) (s (k k) (s (k s) i))) (k k)

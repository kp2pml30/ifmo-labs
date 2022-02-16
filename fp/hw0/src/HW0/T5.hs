module HW0.T5 where

import Numeric.Natural

type Nat a = (a -> a) -> a -> a

nz :: Nat a
nz _ = id

ns :: Nat a -> Nat a
ns n f x = n f $ f x

nplus :: Nat a -> Nat a -> Nat a
nplus a b f x = a f $ b f x

nmult :: Nat a -> Nat a -> Nat a
nmult a b f = a (b f)

nFromNatural :: Natural -> Nat a
nFromNatural 0 = nz
nFromNatural n = ns $ nFromNatural (n - 1)

nToNum :: Num a => Nat a -> a
nToNum n = n (+1) 0

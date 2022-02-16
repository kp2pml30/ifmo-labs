module HW0.T2 where

import Data.Void

import Data.Function ((&))

type Not a = a -> Void

doubleNeg :: a -> Not (Not a)
-- a -> (Not a) -> Void
-- a -> (a -> Void) -> Void
doubleNeg = (&)

reduceTripleNeg :: Not (Not (Not a)) -> Not a
-- (((a -> Void) -> Void) -> Void) -> Not a
-- (((a -> Void) -> Void) -> Void) -> (a -> Void)
-- (((a -> Void) -> Void) -> Void) -> a -> Void
-- (Not (Not (a -> Void)) -> a -> Void
reduceTripleNeg a b = a $ doubleNeg b

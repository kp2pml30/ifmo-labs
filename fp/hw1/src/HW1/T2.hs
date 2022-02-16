module HW1.T2
  ( N (..)
  , nplus
  , nmult
  , nsub
  , ncmp
  , nFromNatural
  , nToNum
  , nEven
  , nOdd
  , ndiv
  , nmod
  ) where

import Data.Maybe
import Numeric.Natural

data N = Z | S N deriving (Show)

infixl 6 `nplus`
infixl 6 `nsub`
infixl 7 `nmult`
infixl 7 `ndiv`

applyTimes :: N -> (a -> a) -> a -> a
applyTimes Z _ x     = x
applyTimes (S a) f x = applyTimes a f (f x)

iterateNth :: (Eq b, Num b) => (a -> a) -> a -> b -> a
iterateNth f x n
  | n == 0    = x
  | otherwise = iterateNth f (f x) (n - 1)

nplus :: N -> N -> N
nplus a = applyTimes a S

nmult :: N -> N -> N
nmult a b = applyTimes a (nplus b) Z

decr :: N -> Maybe N
decr Z     = Nothing
decr (S a) = Just a

nsub :: N -> N -> Maybe N
nsub a b = applyTimes b (>>= decr) (Just a)

ncmp :: N -> N -> Ordering
ncmp a b =
  case nsub a b of
    Nothing -> LT
    Just Z  -> EQ
    _       -> GT

nFromNatural :: Natural -> N
nFromNatural = iterateNth S Z

nToNum :: Num n => N -> n
nToNum a = applyTimes a (+1) 0

nEven :: N -> Bool
nEven a = applyTimes a not True

nOdd :: N -> Bool
nOdd = not . nEven

ndiv :: N -> N -> N
ndiv a b =
  helper Z (a `nsub` b)
  where
    helper x Nothing  = x
    helper x (Just a) = helper (S x) (a `nsub` b)

nmod :: N -> N -> N
nmod a b = fromJust $ a `nsub` a `ndiv` b `nmult` b

module HW1.T7
  ( ListPlus (..)
  , Inclusive (..)
  , DotString (..)
  , Fun (..)
  )  where

import Data.Semigroup (Semigroup (..), (<>))

data ListPlus a = a :+ ListPlus a | Last a deriving (Show)
infixr 5 :+

instance Semigroup (ListPlus a) where
  Last a <> b   = a :+ b
  (a :+ c) <> b = a :+ (c <> b)

data Inclusive a b = This a | That b | Both a b deriving (Show)

instance (Semigroup a, Semigroup b) => Semigroup (Inclusive a b) where
  This a <> This b     = This $ a <> b
  That a <> That b     = That $ a <> b
  This a <> That b     = Both a b
  That b <> This a     = Both a b
  Both a x <> Both b y = Both (a <> b) (x <> y)
  Both a x <> This b   = Both (a <> b) x
  Both a x <> That y   = Both a (x <> y)
  That x <> Both a y   = Both a (x <> y)
  This a <> Both b x   = Both (a <> b) x

newtype DotString = DS String deriving (Show)

instance Semigroup DotString where
  DS "" <> x   = x
  x <> DS ""   = x
  DS a <> DS b = DS $ a ++ "." ++ b

instance Monoid DotString where
  mempty = DS ""

newtype Fun a = F (a -> a)

instance Semigroup (Fun a) where
  F a <> F b = F $ a . b

instance Monoid (Fun a) where
  mempty = F id

module HW2.T4
  ( module HW2.T4
  , module HW2.Expr
  ) where

import Prelude
  ( Applicative (..)
  , Double
  , Functor (..)
  , Monad
  , (>>=))

import Control.Monad (ap)

import HW2.Expr
import HW2.EvalCommon
import HW2.T1

newtype State s a = S { runS :: s -> Annotated s a }

mapState :: (a -> b) -> State s a -> State s b
mapState f o = S \s -> let a :# sn = runS o s in f a :# sn

wrapState :: a -> State s a
wrapState a = S (a :#)

joinState :: State s (State s a) -> State s a
joinState o = S \s -> let a :# sn = runS o s in runS a sn

modifyState :: (s -> s) -> State s ()
modifyState f = S \s -> () :# f s

instance Functor (State s) where
  fmap = mapState

instance Applicative (State s) where
  pure = wrapState
  p <*> q = p `ap` q

instance Monad (State s) where
  m >>= f = joinState (fmap f m)

eval :: Expr -> State [Prim Double] Double
eval = evalCommon modifyState (pure ())

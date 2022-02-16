{-# LANGUAGE ScopedTypeVariables #-}

module HW2.EvalCommon where

import Prelude
  ( Monad
  , Double
  , pure
  , Num(..)
  , Eq(..)
  , (/)
  )
import Control.Monad (when)

import HW2.Expr

evalCommon :: forall m. Monad m =>
  (([Prim Double] -> [Prim Double]) -> m ())
  -> m ()
  -> Expr
  -> m Double
evalCommon modify throwZero = ev
  where
    ev :: Expr -> m Double
    ev (Val a)        = pure a
    ev (Op (Add l r)) = evBop Add (+) l r
    ev (Op (Sub l r)) = evBop Sub (-) l r
    ev (Op (Mul l r)) = evBop Mul (*) l r
    ev (Op (Div l r)) = do
      el <- ev l
      er <- ev r
      when (er == 0) throwZero
      modify (Div el er :)
      pure (el / er)
    ev (Op (Abs a))   = evUop Abs abs a
    ev (Op (Sgn a))   = evUop Sgn signum a
    -- | evaluate binary operator
    evBop
      -- constructor (to put into state)
      :: (Double -> Double -> Prim Double)
      -- evaluator
      -> (Double -> Double -> Double)
      -- left
      -> Expr
      -- right
      -> Expr
      -> m Double
    evBop ctor f l r = do
      el <- ev l
      er <- ev r
      modify (ctor el er :)
      pure (f el er)
    -- | evaluate unary operator
    evUop :: (Double -> Prim Double) -> (Double -> Double) -> Expr -> m Double
    evUop ctor f a = do
      e <- ev a
      modify (ctor e :)
      pure (f e)

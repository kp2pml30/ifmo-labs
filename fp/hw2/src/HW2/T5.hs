module HW2.T5 where

import HW2.T4

-- I still can't use it, right?
import Prelude
  ( Applicative
  , Functor
  , Monad
  , fmap
  , pure,
  (<*>)
  , (>>=)
  , Double
  )

import HW2.EvalCommon

import Control.Monad (ap, when)

import HW2.T1

newtype ExceptState e s a = ES { runES :: s -> Except e (Annotated s a) }

-- | map return of state monad
mapExceptState :: (a -> b) -> ExceptState e s a -> ExceptState e s b
mapExceptState f o =
  ES \s ->
    let r = runES o s in
    case r of
      Error e          -> Error e
      Success (a :# e) -> Success (f a :# e)
wrapExceptState :: a -> ExceptState e s a
wrapExceptState a = ES \s -> Success (a :# s)

-- | evaluate returned state (on success) with modified state
joinExceptState :: ExceptState e s (ExceptState e s a) -> ExceptState e s a
joinExceptState o =
  ES \s ->
    let cse = runES o s in
    case cse of
      Error e           -> Error e
      Success (a :# sn) -> runES a sn

-- | map state component
modifyExceptState :: (s -> s) -> ExceptState e s ()
modifyExceptState f = ES \s -> Success (() :# f s)

-- | monadic throw
throwExceptState :: e -> ExceptState e s a
throwExceptState e = ES \_ -> Error e -- ES . const . Error

instance Functor (ExceptState e s) where
  fmap = mapExceptState

instance Applicative (ExceptState e s) where
  pure = wrapExceptState
  p <*> q = p `ap` q

instance Monad (ExceptState e s) where
  m >>= f = joinExceptState (fmap f m)


data EvaluationError = DivideByZero

type SafeEvalMonad = ExceptState EvaluationError [Prim Double] Double

eval :: Expr -> SafeEvalMonad
eval = evalCommon modifyExceptState (throwExceptState DivideByZero)

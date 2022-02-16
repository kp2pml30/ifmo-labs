{-# LANGUAGE LambdaCase #-}

module HW3.Internal.Eval where

import Control.Applicative
import Control.Monad.Except
import Data.Map (Map)
import Data.Sequence (Seq)

import HW3.Base

type EvalError = Maybe HiError
type HiLst = Seq HiValue
type HiDict = Map HiValue HiValue

newtype (HiMonad m) => EvalMonad m a
  = EvalMonad (ExceptT EvalError m a)
  deriving newtype (Functor, Applicative, Monad, MonadTrans, MonadError EvalError)

instance HiMonad m => HiMonad (EvalMonad m) where
  runAction = lift . runAction

-- | won't continue selecting overloads
throwHi :: HiMonad him => HiError -> EvalMonad him a
throwHi = throwError . Just

-- | will continue selecting overloads
throwArgTypeMismatch :: HiMonad him => EvalMonad him a
throwArgTypeMismatch = throwError Nothing

-- | alternative for overloading selection
instance HiMonad him => Alternative (EvalMonad him) where
  empty = throwArgTypeMismatch
  a <|> b = a `catchError` \case
    Nothing  -> b
    Just err -> throwHi err

runEval :: HiMonad him => EvalMonad him a -> him (Either EvalError a)
runEval (EvalMonad e) = runExceptT e

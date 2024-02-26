module Stella.Lib
	( check
	, ErrorData(..)
	) where

import Control.Applicative
import Control.Monad
import Control.Monad.Except
import Control.Monad.State

import Gen.PrintSyntax ( Print, printTree )

import Data.Either

import Stella.Errs
import Gen.AbsSyntax

data CheckerState
	= CheckerState
	{
	}

data ErrorData
	= ErrorData
	{ code :: Err
	, related :: [(String, String)]
	}

newtype CheckerMonad a
  = CheckerMonad { unCheckerMonad :: StateT CheckerState (Except ErrorData) a }
  deriving newtype (Functor, Applicative, Monad, MonadError ErrorData, MonadState CheckerState)

doCheck :: Program -> CheckerMonad ()
doCheck _ = do
	pure ()

check :: Program -> [ErrorData]
check p = either (:[]) (const []) $ runExcept $ evalStateT (unCheckerMonad $ doCheck p) (CheckerState)

module Stella.Lib
	( check
	, ErrorData(..)
	) where

import Control.Applicative
import Control.Monad
import Control.Monad.Except
import Control.Monad.State

import qualified Gen.PrintSyntax as Printer -- ( Print, printTree )

import Data.Either
import qualified Data.DisjointSet as DisjointSet
import Data.DisjointSet (DisjointSet)

import Stella.Errs
import Gen.AbsSyntax

data CheckerState
	= CheckerState
	{ typeVars :: DisjointSet Int
	}

emptyCheckerState :: CheckerState
emptyCheckerState = CheckerState DisjointSet.empty

data ErrorData
	= ErrorData
	{ code :: Err
	, related :: [(String, String)]
	}

newtype CheckerMonad a
  = CheckerMonad { unCheckerMonad :: StateT CheckerState (Except ErrorData) a }
  deriving newtype (Functor, Applicative, Monad, MonadError ErrorData, MonadState CheckerState)

todo :: CheckerMonad a
todo = throwError $ ErrorData ERROR_TODO []

doCheck :: Program -> CheckerMonad ()
doCheck _ = do
	todo

check :: Program -> [ErrorData]
check p = either (:[]) (const []) $ runExcept $ evalStateT (unCheckerMonad $ doCheck p) emptyCheckerState

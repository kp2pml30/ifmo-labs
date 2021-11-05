module YLex.Base where

import Control.Monad.State
import Control.Monad.Trans.Except
import Control.Monad.Identity
import Control.Monad.Except
import Control.Applicative
import qualified Data.Text as Text

data Position = Position { line :: !Int, col :: !Int, absolute :: !Int } deriving (Eq, Show)

defaultPosition = Position 0 0 0

data LexState us
	= LexState
		{ userState :: us
		, curPos :: !Position
		, rest :: Text.Text
		}
	deriving (Show)

defaultLexState = flip LexState defaultPosition

data LexError = LexError !String !Position deriving (Eq, Show)

newtype LexMonad us a
	= LexMonad (StateT (LexState us) (ExceptT LexError Identity) a)
	deriving newtype (Functor, Monad, Applicative, MonadState (LexState us), MonadError LexError)

instance MonadPlus (LexMonad u) where

throwErrorLE :: String -> Position -> LexMonad us a
throwErrorLE a b = throwError $ LexError a b

throwErrorPos :: Position -> LexMonad us a
throwErrorPos = throwErrorLE ""

parsePosition :: LexMonad us Position
parsePosition = gets curPos

parseError :: LexMonad us a
parseError = parsePosition >>= throwErrorPos

parseErrorStr :: String -> LexMonad us a
parseErrorStr s = parsePosition >>= throwErrorLE s

instance Alternative (LexMonad us) where
	empty = parseError
	a <|> b = do
		prev <- get
		a `catchError` const (put prev >> b)


{-# LANGUAGE DeriveFunctor #-}

module YLex.Lex where

import qualified Data.Text as Text

import YLex.Base
import YLex.Combinators
import Control.Monad
import Control.Monad.State
import Control.Applicative

tokenize :: forall us a. Text.Text -> us -> LexMonad us () -> LexMonad us a -> TokensList a
tokenize t u pre f =
	tokenize' $ defaultLexState u t
	where
		tokenize' !s0 =
			let res = runLexMonad (liftM2 (,) (pre >> gets curPos) parseMonad) s0 in
			case res of
				Left p -> TLError p
				Right ((p, Nothing), _) -> TLEof p
				Right ((p, Just !a), sn) -> TLCons a p (tokenize' sn)
		parseMonad :: LexMonad us (Maybe a)
		parseMonad = (parseEof >> return Nothing) <|> (Just <$> f)

data TokensList a
	= TLEof !Position
	| TLError !LexError
	| TLCons !a !Position (TokensList a)
	deriving (Show, Functor)

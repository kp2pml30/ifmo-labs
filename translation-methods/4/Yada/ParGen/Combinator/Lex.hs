{-# LANGUAGE DeriveFunctor #-}

module Yada.ParGen.Combinator.Lex where

import qualified Data.Text as Text

import Yada.ParGen.Combinator.Base
import Yada.ParGen.Combinator.Combinators
import Control.Monad
import Control.Monad.State
import Control.Applicative

tokenize :: forall us a. LexMonad us () -> LexMonad us a -> us -> Text.Text -> TokensList a
tokenize pre f u t =
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

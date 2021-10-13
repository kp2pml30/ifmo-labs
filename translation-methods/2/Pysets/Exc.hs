module Pysets.Exc where

import Control.Monad.Trans.Except
import Control.Monad.State
import Control.Monad.Identity

import Pysets.Tokens

type PysetsMonad s a = StateT s (ExceptT ParserError Identity) a
runPysetsMonad m = runIdentity . runExceptT . evalStateT m

data ParserError = ParserError String (Maybe Position) deriving (Eq, Show)

showParserError (ParserError s p) = s ++ " at " ++ maybe "<EOF>" showPosition p

data TokenList = ListEof | TokenListCons Token TokenList | ListError ParserError deriving (Eq, Show)

tokenListConverter l r =
	tokenlistConverter' l
	where
		tokenlistConverter' [] = r
		tokenlistConverter' (x:xs) = TokenListCons x (tokenlistConverter' xs)

tokenListConverter2 :: TokenList -> ([Token], Maybe ParserError)
tokenListConverter2 ListEof = ([], Nothing)
tokenListConverter2 (TokenListCons h t) =
	let (nt, m) = tokenListConverter2 t in
	(h:nt, m)
tokenListConverter2 (ListError e) = ([], Just e)


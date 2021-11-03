{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import YLex.Base
import YLex.Lex
import YLex.Combinators

import YPar.Par

import qualified Data.Text as Text
import Data.Char
import qualified Data.Map as Map
import Control.Monad
import Control.Applicative
import Control.Monad.Extra
import Data.String (IsString(..))

data Token
	= TLParen
	| TRParen
	| TMinus
	| TAnd
	| TOr
	| TXor
	| TNot
	| TIn
	| TName Text.Text
	deriving (Show)

skipWs = void $ parseStr isSpace

parseSymbol c r = do
	a <- parseChar
	if a == c
	then return r
	else parseError

parseLParen = parseSymbol '(' TLParen
parseRParen = parseSymbol ')' TRParen

parseWord = do
	r <- parseStr isAsciiLower
	when (Text.null r) parseError
	return $ r

operators :: Map.Map Text.Text Token
operators = Map.fromList [("and", TAnd), ("or", TOr), ("xor", TXor), ("not", TNot), ("in", TIn)]

parseOpName = do
	s <- parseWord
	maybe (return $ TName s) return (Map.lookup s operators)

parseMain
	=   parseLParen
	<|> parseRParen
	<|> parseOpName

main = do
	print $ tokenize "  abc and or (ddd\n) errR a" () skipWs parseMain
	s <- getContents
	print $ parseGrammar (fromString s)
	return ()

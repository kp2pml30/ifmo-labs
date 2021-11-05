{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Task2Common
import Task2

import YLex.Base
import YLex.Lex
import YLex.Combinators

import YPar.Par

import qualified Data.Text as Text
import qualified Data.Text.IO as TextIO
import System.IO (hPutStrLn, stderr)
import System.Exit (exitFailure)
import Data.Char
import qualified Data.Map as Map
import Control.Monad
import Control.Applicative
import Data.String (IsString(..))

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
	let _ = tokenize "  abc and or (ddd\n) errR a" () skipWs parseMain
	s <- getContents
	case processGrammar <$> parseGrammar (fromString s) of
		Left p -> hPutStrLn stderr ("Error occured " ++ show p) >> exitFailure
		Right r -> TextIO.putStrLn r
	return ()

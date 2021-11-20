{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Yada.ParGen.Lex

import qualified Data.Text.IO as TextIO
import System.IO (hPutStrLn, stderr)
import System.Exit (exitFailure)

main = do
	s <- TextIO.getContents
	case processLexGrammar s of
		Left p -> hPutStrLn stderr ("Error occured " ++ show p) >> exitFailure
		Right r -> TextIO.putStrLn r

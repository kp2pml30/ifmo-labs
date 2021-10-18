{-# LANGUAGE OverloadedStrings #-}

module Main where

import Pysets.Lex
import Pysets.Par
import Pysets.Exc
import Pysets.Expr
import System.Process
import System.IO

import qualified Data.Text as T

main :: IO ()
main = do
	str <- getContents
	let toks = tokenize $ T.pack str
	print $ tokenListConverter2 toks
	let parsed = parse toks
	case parsed of
		Left err -> print err
		Right par -> do
			print par
			let proc = shell "dot -Tpng | feh -"
			(Just inp, _, _, _) <- createProcess proc { std_in = CreatePipe }
			hPutStr inp $ expr2Dot par
			hClose inp

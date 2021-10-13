{-# LANGUAGE OverloadedStrings #-}

module Main where

import Pysets.Lex
import Pysets.Par
import Pysets.Exc

import qualified Data.Text as T

main :: IO ()
main = do
	str <- getContents
	let toks = tokenize $ T.pack str
	print $ tokenListConverter2 toks
	print $ parse toks

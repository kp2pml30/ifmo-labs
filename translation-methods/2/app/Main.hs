{-# LANGUAGE OverloadedStrings #-}

module Main where

import Pysets.Lex
import Pysets.Par

import qualified Data.Text as T

main :: IO ()
main = do
	let tests = ["a", "a b", "(a)", "((a))", "()", "a and b and c", "a and (b and c)", "a and", "a in b", "a not in b", "a not b"]
	mapM_ (\(i, t) -> do
		putStrLn $ show i ++ ".\t" ++ t
		let toks = tokenize $ T.pack t
		print toks
		print $ parse toks)
		(zip [1 :: Int ..] tests)

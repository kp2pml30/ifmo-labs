module Main where

import Obfuscation.Lex
import Obfuscation.Par
import Obfuscation.Obf

import System.Random
import System.Environment (getArgs)

main :: IO ()
main = do
	args <- getArgs
	s <- getContents
	rnd <- getStdGen
	let seeds = randomRs (10 :: Int, 2048) rnd
	let toks = alexScanTokens s
	-- print toks
	let mapper = case args of
		[] -> insI1O0
		["--id"] -> insId
		_ -> undefined
	let expr = evalParse mapper $ parse toks
	putStrLn expr

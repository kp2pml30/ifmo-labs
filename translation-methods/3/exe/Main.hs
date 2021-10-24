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
	let eval = case args of
		[] -> evalParseRnd seeds insI1O0
		["--no-random"] -> evalParse insI1O0
		["--id"] -> evalParse insId
		_ -> error "unknown options"
	let expr = eval $ parse toks
	putStrLn expr

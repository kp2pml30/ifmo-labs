module Main (main) where

import Stella.Lib
import Gen.AbsSyntax

import System.Environment ( getArgs )
import System.Exit        ( exitFailure, exitSuccess )
import Control.Monad
import System.IO

import Gen.AbsSyntax   ()
import Gen.LexSyntax   ( Token, mkPosToken )
import Gen.ParSyntax   ( pProgram, myLexer )
import Gen.SkelSyntax  ()

type Err        = Either String
type ParseFun a = [Token] -> Err a

runFile :: ParseFun Program -> FilePath -> IO ()
runFile p f = readFile f >>= run p

run :: ParseFun Program -> String -> IO ()
run p s =
	case p ts of
		Left err -> do
			putStrLn "Parse failed..."
			putStrLn "Tokens:"
			mapM_ (putStrLn . showPosToken . mkPosToken) ts
			putStrLn err
			exitFailure
		Right tree -> do
			showTree tree
			case check tree of
				[] -> exitSuccess
				lst -> do
					forM_ lst $ \ErrorData {..} -> do
						hPutStrLn stderr $ show code
						forM_ related $ \(header, text) -> do
							hPutStrLn stderr $ "\t" ++ header
							hPutStrLn stderr $ "\t" ++ text
							hPutStrLn stderr ""
					exitFailure
	where
		ts = myLexer s
		showPosToken ((l,c),t) = concat [ show l, ":", show c, "\t", show t ]

showTree :: Program -> IO ()
showTree tree = do
	putStrLn $ show tree

main :: IO ()
main = do
	args <- getArgs
	case args of
		[] -> getContents >>= run pProgram
		fs -> mapM_ (runFile pProgram) fs

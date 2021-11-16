module Obfuscation.Par where

import System.IO.Unsafe (unsafePerformIO)

import qualified Obfuscation.ParGen as PG

import Obfuscation.Obf
import Obfuscation.Tokens
import YLex.Lex

parse :: TokensList Token -> [Md]
parse lst = case PG.parse lst of
	Right r -> r
	Left l -> unsafePerformIO (print lst >> return (error $ show l))

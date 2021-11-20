{-# LANGUAGE OverloadedStrings #-}
module Main where

import qualified Par
import qualified Lex

import Yada.ParGen.Combinator

import qualified Data.Text as Text
import Control.Monad
import Data.Char

import Test.HUnit
import Test.Framework
import Test.Framework.Providers.HUnit

import Data.Bifunctor

skipWs = void $ parseWhile isSpace

getResult s = bimap lexErrorPos show $ Par.parse $ tokenize skipWs Lex.parse () s

myTest s a = do
	assertEqual (Text.unpack s ++ " parse result") (getResult s) a

main = do
	let
		exprs =
			[ "a"
			, "loooong"
			, "andmore"
			, "BAD"
			, "ok or BAD"
			, "a b"
			, "(a)"
			, "((a))"
			, "()"
			, "a and b and c"
			, "a and (b and c)"
			, "a and"
			, "a in b"
			, "a not in b"
			, "a not b"
			, "not a"
			, "not not a"
			, "p or r xor e and c in e in n in d not in e in n not in c not in e"
			]
		answers =
			[ Right "a" -- "a"
			, Right "loooong" -- "loooong"
			, Right "andmore" -- "andmore"
			, Left (Position {line = 0, col = 0, absolute = 0}) -- "BAD"
			, Left (Position {line = 0, col = 6, absolute = 6}) -- "ok or BAD"
			, Left (Position {line = 0, col = 2, absolute = 2}) -- "a b"
			, Right "a" -- "(a)"
			, Right "a" -- "((a))"
			, Left (Position {line = 0, col = 1, absolute = 1}) -- "()"
			, Right "((a&b)&c)" -- "a and b and c"
			, Right "(a&(b&c))" -- "a and (b and c)"
			, Left (Position {line = 0, col = 5, absolute = 5}) -- "a and"
			, Right "(a\8712b)" -- "a in b"
			, Right "!(a\8712b)" -- "a not in b"
			, Left (Position {line = 0, col = 7, absolute = 7}) -- "a not b"
			, Right "!a" -- "not a"
			, Right "!!a" -- "not not a"
			, Right "!(!((!(((((p|(r^(e&c)))\8712e)\8712n)\8712d)\8712e)\8712n)\8712c)\8712e)" -- "p or r xor e and c in e in n in d not in e in n not in c not in e"
			]
		tests = zipWith (\str ans -> testCase (Text.unpack str) $ myTest str ans) exprs answers
	-- mapM_ (\s -> putStrLn $ ", " <> show (getResult s) <> " -- " <> show s) exprs
	defaultMainWithOpts tests mempty

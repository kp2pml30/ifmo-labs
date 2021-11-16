module Main (main) where

import Test.HUnit
import Test.Framework
import Test.Framework.Providers.HUnit

import Control.Monad.Reader (runReader)

import Par
import Lex

myTest :: String -> Tree -> Assertion
myTest s exp =
	let res = flip runReader 0 <$> parse (scan s) in
	assertEqual "bad eval" (Right exp) res

main = do
	let
		exprs =
			[ ("n", Leaf)
			, ("bbnnn", Branch (Branch Leaf Leaf 1) Leaf 0)
			]
	let tests = map (\(s, n) -> testCase s $ myTest s n) exprs
	defaultMainWithOpts tests mempty

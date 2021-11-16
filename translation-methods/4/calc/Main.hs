module Main (main) where

import Test.HUnit
import Test.Framework
import Test.Framework.Providers.HUnit

import Par
import Lex

myTest s exp =
	let res = parse $ scan s in
	assertEqual "bad eval" exp (either (const Nothing) Just res)

main = do
	let
		exprs =
			[ ("0", Just 0)
			, ("1 + 2", Just 3)
			, ("1 +", Nothing)
			, ("1 - 2 - 3", Just $ negate 4)
			, ("1 + 2 * 3", Just 7)
			, ("(1 + 2) * 3", Just 9)
			, ("2 * 3 + 4 * 5", Just 26)
			, ("", Nothing)
			, ("1.", Nothing)
			, ("+5.", Nothing)
			, ("1 -- 5.", Nothing)
			, ("1 - - 5.", Nothing)
			]
	let tests = map (\(s, n) -> testCase s $ myTest s n) exprs
	defaultMainWithOpts tests mempty

{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Test.HUnit
import Test.Framework
import Test.Framework.Providers.HUnit

import Data.Char
import Control.Monad
import qualified Data.Text as Text

import Yada.ParGen.Combinator

import qualified Par
import qualified Lex

skipWs = void $ parseWhile isSpace

myTest s exp =
	let res = Par.parse $ tokenize skipWs Lex.parse () s in
	assertEqual "bad eval" exp (either (const Nothing) Just res)

main = do
	let
		exprs :: [(Text.Text, Maybe Int)]
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
			, ("1 -- 5", Just 6)
			, ("1 ---5", Just $ negate 4)
			, ("1 - - 5.", Nothing)
			, ("2 ** 2 ** 3", Just 256)
			, ("2 ** 3 ** 2", Just 512)
			, ("2 ** 3 * 3 ** 2", Just 72)
			]
	let tests = map (\(s, n) -> testCase (Text.unpack s) $ myTest s n) exprs
	defaultMainWithOpts tests mempty

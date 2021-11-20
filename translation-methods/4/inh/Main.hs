module Main (main) where

import Test.HUnit
import Test.Framework
import Test.Framework.Providers.HUnit

import Control.Monad.Reader (runReader)
import Control.Monad
import Data.Char
import qualified Data.Text as Text

import Yada.ParGen.Combinator

import qualified Par
import qualified Lex
import Token

myTest :: String -> Tree -> Assertion
myTest s exp =
	let res = flip runReader 0 <$> Par.parse (tokenize skipWs Lex.parse () $ Text.pack s) in
	assertEqual "bad eval" (Right exp) res

skipWs = void $ parseWhile isSpace

main = do
	let
		exprs =
			[ ("n", Leaf)
			, ("bbnnn", Branch (Branch Leaf Leaf 1) Leaf 0)
			]
	let tests = map (\(s, n) -> testCase s $ myTest s n) exprs
	defaultMainWithOpts tests mempty

module Main (main) where

import Test.HUnit
import Test.Framework
import Test.Framework.Providers.HUnit
import Data.Monoid
import Control.Monad
import Data.Text (Text)
import qualified Data.Text as T

import Pysets.Par
import Pysets.Lex
import Pysets.Tokens
import Pysets.Expr
import Pysets.Exc

lrmap :: Either ParserError Expr -> Either (Maybe Position) String
lrmap (Left (ParserError _ p)) = Left p
lrmap (Right e) = Right $ show e

displayTests :: [String] -> IO ()
displayTests exprs = do
	let toks = map tokenize (T.pack <$> exprs)
	print $ map tokenListConverter2 toks
	print $ map (lrmap . parse) toks

-- myTest :: (String, ([Token], Maybe Position), Either (Maybe Position) String) -> Assertion
myTest (s, t, p) = do
	let toks = tokenize (T.pack s)
	assertEqual (s ++ " tokenization") (tokenListConverter2 toks) t
	let par = lrmap $ parse toks
	assertEqual (s ++ " parse result") par p

main :: IO ()
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
			]
		tokenAnswers = [([TName {tName = "a", tPos = Position {line = 0, col = 0, absolute = 0}}],Nothing),([TName {tName = "loooong", tPos = Position {line = 0, col = 0, absolute = 0}}],Nothing),([TName {tName = "andmore", tPos = Position {line = 0, col = 0, absolute = 0}}],Nothing),([],Just (ParserError "can't tokenize" (Just (Position {line = 0, col = 0, absolute = 0})))),([TName {tName = "ok", tPos = Position {line = 0, col = 0, absolute = 0}},TOr {tPos = Position {line = 0, col = 3, absolute = 3}}],Just (ParserError "can't tokenize" (Just (Position {line = 0, col = 6, absolute = 6})))),([TName {tName = "a", tPos = Position {line = 0, col = 0, absolute = 0}},TName {tName = "b", tPos = Position {line = 0, col = 2, absolute = 2}}],Nothing),([TLParen {tPos = Position {line = 0, col = 0, absolute = 0}},TName {tName = "a", tPos = Position {line = 0, col = 1, absolute = 1}},TRParen {tPos = Position {line = 0, col = 2, absolute = 2}}],Nothing),([TLParen {tPos = Position {line = 0, col = 0, absolute = 0}},TLParen {tPos = Position {line = 0, col = 1, absolute = 1}},TName {tName = "a", tPos = Position {line = 0, col = 2, absolute = 2}},TRParen {tPos = Position {line = 0, col = 3, absolute = 3}},TRParen {tPos = Position {line = 0, col = 4, absolute = 4}}],Nothing),([TLParen {tPos = Position {line = 0, col = 0, absolute = 0}},TRParen {tPos = Position {line = 0, col = 1, absolute = 1}}],Nothing),([TName {tName = "a", tPos = Position {line = 0, col = 0, absolute = 0}},TAnd {tPos = Position {line = 0, col = 2, absolute = 2}},TName {tName = "b", tPos = Position {line = 0, col = 6, absolute = 6}},TAnd {tPos = Position {line = 0, col = 8, absolute = 8}},TName {tName = "c", tPos = Position {line = 0, col = 12, absolute = 12}}],Nothing),([TName {tName = "a", tPos = Position {line = 0, col = 0, absolute = 0}},TAnd {tPos = Position {line = 0, col = 2, absolute = 2}},TLParen {tPos = Position {line = 0, col = 6, absolute = 6}},TName {tName = "b", tPos = Position {line = 0, col = 7, absolute = 7}},TAnd {tPos = Position {line = 0, col = 9, absolute = 9}},TName {tName = "c", tPos = Position {line = 0, col = 13, absolute = 13}},TRParen {tPos = Position {line = 0, col = 14, absolute = 14}}],Nothing),([TName {tName = "a", tPos = Position {line = 0, col = 0, absolute = 0}},TAnd {tPos = Position {line = 0, col = 2, absolute = 2}}],Nothing),([TName {tName = "a", tPos = Position {line = 0, col = 0, absolute = 0}},TIn {tPos = Position {line = 0, col = 2, absolute = 2}},TName {tName = "b", tPos = Position {line = 0, col = 5, absolute = 5}}],Nothing),([TName {tName = "a", tPos = Position {line = 0, col = 0, absolute = 0}},TNot {tPos = Position {line = 0, col = 2, absolute = 2}},TIn {tPos = Position {line = 0, col = 6, absolute = 6}},TName {tName = "b", tPos = Position {line = 0, col = 9, absolute = 9}}],Nothing),([TName {tName = "a", tPos = Position {line = 0, col = 0, absolute = 0}},TNot {tPos = Position {line = 0, col = 2, absolute = 2}},TName {tName = "b", tPos = Position {line = 0, col = 6, absolute = 6}}],Nothing),([TNot {tPos = Position {line = 0, col = 0, absolute = 0}},TName {tName = "a", tPos = Position {line = 0, col = 4, absolute = 4}}],Nothing),([TNot {tPos = Position {line = 0, col = 0, absolute = 0}},TNot {tPos = Position {line = 0, col = 4, absolute = 4}},TName {tName = "a", tPos = Position {line = 0, col = 8, absolute = 8}}],Nothing)]
		parserAnswers = [Right "a",Right "loooong",Right "andmore",Left (Just (Position {line = 0, col = 0, absolute = 0})),Left (Just (Position {line = 0, col = 6, absolute = 6})),Left (Just (Position {line = 0, col = 2, absolute = 2})),Right "a",Right "a",Left (Just (Position {line = 0, col = 1, absolute = 1})),Right "((a&b)&c)",Right "(a&(b&c))",Left Nothing,Right "!(a\8712b)",Right "!(a\8712b)",Left (Just (Position {line = 0, col = 6, absolute = 6})),Right "!a",Right "!!a"]
		zipped = zip3 exprs tokenAnswers parserAnswers
		tests = map (\a@(s,_,_) -> testCase s (myTest a)) zipped
	-- displayTests exprs
	defaultMainWithOpts tests mempty

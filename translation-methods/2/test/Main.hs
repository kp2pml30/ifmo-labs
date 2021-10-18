module Main (main) where

import Test.HUnit
import Test.Framework
import Test.Framework.Providers.HUnit
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
			, "p or r xor e and c in e in n in d not in e in n not in c not in e"
			]
		tokenAnswers = [([TName {tName = "a", tPos = Position {line = 0, col = 0, absolute = 0}}],Nothing),([TName {tName = "loooong", tPos = Position {line = 0, col = 0, absolute = 0}}],Nothing),([TName {tName = "andmore", tPos = Position {line = 0, col = 0, absolute = 0}}],Nothing),([],Just (ParserError "can't tokenize" (Just (Position {line = 0, col = 0, absolute = 0})))),([TName {tName = "ok", tPos = Position {line = 0, col = 0, absolute = 0}},TOr {tPos = Position {line = 0, col = 3, absolute = 3}}],Just (ParserError "can't tokenize" (Just (Position {line = 0, col = 6, absolute = 6})))),([TName {tName = "a", tPos = Position {line = 0, col = 0, absolute = 0}},TName {tName = "b", tPos = Position {line = 0, col = 2, absolute = 2}}],Nothing),([TLParen {tPos = Position {line = 0, col = 0, absolute = 0}},TName {tName = "a", tPos = Position {line = 0, col = 1, absolute = 1}},TRParen {tPos = Position {line = 0, col = 2, absolute = 2}}],Nothing),([TLParen {tPos = Position {line = 0, col = 0, absolute = 0}},TLParen {tPos = Position {line = 0, col = 1, absolute = 1}},TName {tName = "a", tPos = Position {line = 0, col = 2, absolute = 2}},TRParen {tPos = Position {line = 0, col = 3, absolute = 3}},TRParen {tPos = Position {line = 0, col = 4, absolute = 4}}],Nothing),([TLParen {tPos = Position {line = 0, col = 0, absolute = 0}},TRParen {tPos = Position {line = 0, col = 1, absolute = 1}}],Nothing),([TName {tName = "a", tPos = Position {line = 0, col = 0, absolute = 0}},TAnd {tPos = Position {line = 0, col = 2, absolute = 2}},TName {tName = "b", tPos = Position {line = 0, col = 6, absolute = 6}},TAnd {tPos = Position {line = 0, col = 8, absolute = 8}},TName {tName = "c", tPos = Position {line = 0, col = 12, absolute = 12}}],Nothing),([TName {tName = "a", tPos = Position {line = 0, col = 0, absolute = 0}},TAnd {tPos = Position {line = 0, col = 2, absolute = 2}},TLParen {tPos = Position {line = 0, col = 6, absolute = 6}},TName {tName = "b", tPos = Position {line = 0, col = 7, absolute = 7}},TAnd {tPos = Position {line = 0, col = 9, absolute = 9}},TName {tName = "c", tPos = Position {line = 0, col = 13, absolute = 13}},TRParen {tPos = Position {line = 0, col = 14, absolute = 14}}],Nothing),([TName {tName = "a", tPos = Position {line = 0, col = 0, absolute = 0}},TAnd {tPos = Position {line = 0, col = 2, absolute = 2}}],Nothing),([TName {tName = "a", tPos = Position {line = 0, col = 0, absolute = 0}},TIn {tPos = Position {line = 0, col = 2, absolute = 2}},TName {tName = "b", tPos = Position {line = 0, col = 5, absolute = 5}}],Nothing),([TName {tName = "a", tPos = Position {line = 0, col = 0, absolute = 0}},TNot {tPos = Position {line = 0, col = 2, absolute = 2}},TIn {tPos = Position {line = 0, col = 6, absolute = 6}},TName {tName = "b", tPos = Position {line = 0, col = 9, absolute = 9}}],Nothing),([TName {tName = "a", tPos = Position {line = 0, col = 0, absolute = 0}},TNot {tPos = Position {line = 0, col = 2, absolute = 2}},TName {tName = "b", tPos = Position {line = 0, col = 6, absolute = 6}}],Nothing),([TNot {tPos = Position {line = 0, col = 0, absolute = 0}},TName {tName = "a", tPos = Position {line = 0, col = 4, absolute = 4}}],Nothing),([TNot {tPos = Position {line = 0, col = 0, absolute = 0}},TNot {tPos = Position {line = 0, col = 4, absolute = 4}},TName {tName = "a", tPos = Position {line = 0, col = 8, absolute = 8}}],Nothing),([TName {tName = "p", tPos = Position {line = 0, col = 0, absolute = 0}},TOr {tPos = Position {line = 0, col = 2, absolute = 2}},TName {tName = "r", tPos = Position {line = 0, col = 5, absolute = 5}},TXor {tPos = Position {line = 0, col = 7, absolute = 7}},TName {tName = "e", tPos = Position {line = 0, col = 11, absolute = 11}},TAnd {tPos = Position {line = 0, col = 13, absolute = 13}},TName {tName = "c", tPos = Position {line = 0, col = 17, absolute = 17}},TIn {tPos = Position {line = 0, col = 19, absolute = 19}},TName {tName = "e", tPos = Position {line = 0, col = 22, absolute = 22}},TIn {tPos = Position {line = 0, col = 24, absolute = 24}},TName {tName = "n", tPos = Position {line = 0, col = 27, absolute = 27}},TIn {tPos = Position {line = 0, col = 29, absolute = 29}},TName {tName = "d", tPos = Position {line = 0, col = 32, absolute = 32}},TNot {tPos = Position {line = 0, col = 34, absolute = 34}},TIn {tPos = Position {line = 0, col = 38, absolute = 38}},TName {tName = "e", tPos = Position {line = 0, col = 41, absolute = 41}},TIn {tPos = Position {line = 0, col = 43, absolute = 43}},TName {tName = "n", tPos = Position {line = 0, col = 46, absolute = 46}},TNot {tPos = Position {line = 0, col = 48, absolute = 48}},TIn {tPos = Position {line = 0, col = 52, absolute = 52}},TName {tName = "c", tPos = Position {line = 0, col = 55, absolute = 55}},TNot {tPos = Position {line = 0, col = 57, absolute = 57}},TIn {tPos = Position {line = 0, col = 61, absolute = 61}},TName {tName = "e", tPos = Position {line = 0, col = 64, absolute = 64}}],Nothing)]
		parserAnswers = [Right "a",Right "loooong",Right "andmore",Left (Just (Position {line = 0, col = 0, absolute = 0})),Left (Just (Position {line = 0, col = 6, absolute = 6})),Left (Just (Position {line = 0, col = 2, absolute = 2})),Right "a",Right "a",Left (Just (Position {line = 0, col = 1, absolute = 1})),Right "((a&b)&c)",Right "(a&(b&c))",Left Nothing,Right "(a\8712b)",Right "!(a\8712b)",Left (Just (Position {line = 0, col = 6, absolute = 6})),Right "!a",Right "!!a",Right "!(!((!(((((p|(r^(e&c)))\8712e)\8712n)\8712d)\8712e)\8712n)\8712c)\8712e)"]
		zipped = zip3 exprs tokenAnswers parserAnswers
		tests = map (\a@(s,_,_) -> testCase s (myTest a)) zipped
	-- displayTests exprs
	defaultMainWithOpts tests mempty

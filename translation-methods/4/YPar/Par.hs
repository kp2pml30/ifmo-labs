{-# LANGUAGE OverloadedStrings #-}

module YPar.Par (Grammar(..), parseGrammar) where

import qualified Data.Text as Text
import Data.Maybe
import Data.Char
import Control.Applicative
import Control.Monad
import Control.Monad.Extra

import YLex.Base
import YLex.Combinators

data Grammar
	= Grammar
		{ nonTerminals :: [(Text.Text, Text.Text)]
		, terminals :: [(Text.Text, [([Text.Text], Text.Text)])]
		}
	deriving (Eq, Show)

skipWs = parseStr isSpace >> noFail (parseCharIf (== '#') >> parseStr (/= '\n') >> skipWs)

parseRest = parseStr (/= '\n')

parseCase = do
	skipWs
	n <- ensureNotEmpty $ parseStr isAsciiLower
	skipWs
	ensureString "<=="
	skipWs
	r <- parseRest
	return (n, r)

parseRule = do
	skipWs
	liftM2 (,)
		(ensureNotEmpty $ parseStr isAsciiUpper)
		(some parseAlt)
	where
		parseAlt = do
			skipWs
			ensureString "|"
			liftM2 (,)
				(some (skipWs >> (parseStrNE isAsciiUpper <|> parseStrNE isAsciiLower)))
				(skipWs >> ensureString "==>" >> skipWs >> parseRest)

-- parseGrammar :: Text.Text -> Either Position Grammar
parseGrammar t = fst <$> runLexMonad
		(do
			r <- liftM2 Grammar
				(some parseCase)
				(some parseRule)
			skipWs
			parseEof
			return r)
		(defaultLexState () t)

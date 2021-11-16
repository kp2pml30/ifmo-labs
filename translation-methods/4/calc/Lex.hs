module Lex (Token (..), scan) where

import qualified Data.Text as Text
import Control.Applicative
import Data.Functor
import Data.Char

import YLex.Base
import YLex.Combinators
import YLex.Lex

data Token
	= TNum Int
	| TLParen
	| TRParen
	| TMul
	| TDiv
	| TAdd
	| TSub
	deriving (Eq, Show)


parseMain :: LexMonad () Token
parseMain = empty
	<|> parseCharIf (== '(') $> TLParen
	<|> parseCharIf (== ')') $> TRParen
	<|> parseCharIf (== '+') $> TAdd
	<|> parseCharIf (== '-') $> TSub
	<|> parseCharIf (== '*') $> TMul
	<|> parseCharIf (== '/') $> TDiv
	<|> TNum . read . Text.unpack <$> parseStrNE isDigit

skipWs = void $ parseStr isSpace

scan :: String -> TokensList Token
scan s = tokenize (Text.pack s) () skipWs parseMain


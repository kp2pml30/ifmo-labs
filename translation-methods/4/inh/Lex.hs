module Lex (Token (..), Tree(..), scan) where

import qualified Data.Text as Text
import Control.Applicative
import Data.Functor
import Data.Char

import YLex.Base
import YLex.Combinators
import YLex.Lex

data Token
	= TB
	| TN
	deriving (Eq, Show)

data Tree
	= Leaf
	| Branch Tree Tree Int
	deriving (Eq, Show)

parseMain :: LexMonad () Token
parseMain = empty
	<|> parseCharIf (== 'b') $> TB
	<|> parseCharIf (== 'n') $> TN

skipWs = void $ parseStr isSpace

scan :: String -> TokensList Token
scan s = tokenize (Text.pack s) () skipWs parseMain


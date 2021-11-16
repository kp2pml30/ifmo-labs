module Obfuscation.Lex (alexScanTokens) where

import qualified Data.Text as Text
import Control.Applicative
import Data.Functor
import Data.Function (on)
import Data.Char

import YLex.Base
import YLex.Combinators
import YLex.Lex
import Obfuscation.Tokens

parseMain :: LexMonad () Token
parseMain = empty
	<|> parseCharIf (== '(') $> TLParen
	<|> parseCharIf (== ')') $> TRParen
	<|> parseCharIf (== '{') $> TLCParen
	<|> parseCharIf (== '}') $> TRCParen
	<|> parseCharIf (== '=') $> TSet
	<|> parseCharIf (== '+') $> TAdd
	<|> parseCharIf (== '-') $> TSub
	<|> parseCharIf (== '*') $> TMul
	<|> parseCharIf (== '/') $> TDiv
	<|> parseCharIf (== ',') $> TComma
	<|> parseCharIf (== ';') $> TSColon
	<|> TLiteral . (\s -> '"' : s ++ "\"") . Text.unpack <$> (parseCharIf (== '"') *> parseStr (/= '"') <* parseCharIf (== '"'))
	<|> TLiteral . Text.unpack <$> parseStrNE isDigit
	<|> TName <$> liftA2 ((++) `on` Text.unpack) (parseStrNE isAlpha) (parseStr isAlphaNum)

skipWs = void $ parseStr isSpace

alexScanTokens :: String -> TokensList Token
alexScanTokens s = tokenize (Text.pack s) () skipWs parseMain

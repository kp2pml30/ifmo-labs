module Common where

import qualified Data.Text as Text

data Token
	= TLParen
	| TRParen
	| TMinus
	| TAnd
	| TOr
	| TXor
	| TNot
	| TIn
	| TName Text.Text
	deriving (Show)


module Obfuscation.Tokens where

data Token
	= TLiteral String
	| TName String
	| TSColon
	| TLParen
	| TRParen
	| TLCParen
	| TRCParen
	| TComma
	| TMul
	| TDiv
	| TAdd
	| TSub
	| TSet
	deriving (Eq, Show)


module Token where

data Token
	= TNum Int
	| TLParen
	| TRParen
	| TMul
	| TDiv
	| TAdd
	| TSub
	deriving (Eq, Show)


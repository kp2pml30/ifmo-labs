module Token where

data Token
	= TNum Int
	| TLParen
	| TRParen
	| TPow
	| TMul
	| TDiv
	| TAdd
	| TSub
	deriving (Eq, Show)


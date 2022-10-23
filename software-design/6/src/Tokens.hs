module Tokens where

data Op
	= Add
	| Sub
	| Mul
	| Div
	deriving (Eq, Ord, Enum, Bounded)

instance Show Op where
	show =
		\case
			Add -> "+"
			Sub -> "-"
			Mul -> "*"
			Div -> "/"


data Token a
	= TOp Op
	| TNum a
	| TLpar
	| TRpar
	deriving (Show, Eq)

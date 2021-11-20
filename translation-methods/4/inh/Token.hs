module Token where

data Token
	= TB
	| TN
	deriving (Eq, Show)

data Tree
	= Leaf
	| Branch Tree Tree Int
	deriving (Eq, Show)

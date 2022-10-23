module Ast where

import Tokens

data Ast a
	= AOp (Ast a) Op (Ast a)
	| ANum a
	deriving (Show, Eq)


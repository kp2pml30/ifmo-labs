{-# LANGUAGE TemplateHaskell #-}

module Pysets.Tokens where

import Pysets.TH

data Position = Position { line :: !Int, col :: !Int, absolute :: !Int } deriving (Eq, Show)

class Pos a where
	position :: a -> Position

showPosition Position { line, col } = show line ++ ":" ++ show col

data Token
	= TLParen { tPos :: !Position }
	| TRParen { tPos :: !Position }
	| TAnd { tPos :: !Position }
	| TOr { tPos :: !Position }
	| TXor { tPos :: !Position }
	| TNot { tPos :: !Position }
	| TIn { tPos :: !Position }
	| TName { tName :: !String, tPos :: !Position }
	deriving (Eq, Show)

deriveIs ''Token

instance Pos Token where
	position = tPos

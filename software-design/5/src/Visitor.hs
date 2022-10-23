{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}
module Visitor where

import Tokens
import Ast

-- oop pattern matching
class Visitor a e v where
	visitNum :: a -> v -> e
	visitOp :: Ast a -> Op -> Ast a -> v -> e

visit :: Visitor a e v => Ast a -> v -> e
visit a v =
	case a of
		ANum n -> visitNum n v
		AOp l o r -> visitOp l o r v

data PAtom a
	= PANum a
	| PAOp Op
	deriving (Show)

data ToPolVis = ToPolVis

instance Visitor a [PAtom a] ToPolVis where
	visitNum n _ = [PANum n]
	visitOp l op r v = PAOp op : (visit r v ++ visit l v)

data PrintVis = PrintVis

instance (Show a) => Visitor a String PrintVis where
	visitNum n _ = show n
	visitOp l op r v = "(" ++ visit l v ++ show op ++ visit r v ++ ")"

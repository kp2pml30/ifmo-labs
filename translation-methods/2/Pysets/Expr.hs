module Pysets.Expr where

import Pysets.Tokens

data Expr
	= Not { expr :: Expr, ePos :: Position }
	| And { lexpr :: Expr, rexpr :: Expr, ePos :: Position }
	| Or { lexpr :: Expr, rexpr :: Expr, ePos :: Position }
	| Xor { lexpr :: Expr, rexpr :: Expr, ePos :: Position }
	| In { lexpr :: Expr, rexpr :: Expr, ePos :: Position }
	| Name { name :: String, ePos :: Position }
	deriving (Eq)

instance Show Expr where
	show Not {..} = "!" ++ show expr
	show e@And {} = shB "&" e
	show e@Or {} = shB "|" e
	show e@Xor {} = shB "^" e
	show e@In {} = shB "∈" e
	show Name{..} = name

shB c e = "(" ++ show (lexpr e) ++ c ++ show (rexpr e) ++ ")"

instance Pos Expr where
	position = ePos


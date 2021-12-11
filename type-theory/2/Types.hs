module Types where

data Token
	= TIndent !Int
	| TArr
	| TAssign
	| TColon
	| TDot
	| TComma
	| TCtx
	| TLPar
	| TRPar
	| TVar !String
	| TLet
	| TIn
	| TLam
	| TForall
	| TRule !Int
	deriving (Eq, Show)

data TypedExpr = TypedExpr Expr Type deriving(Eq, Show)

data Type
	= MType Monotype
	| Forall String Type
	deriving (Eq, Show)

isMonotype (MType _) = True
isMonotype _ = False

data Monotype
	= Type String
	| Arr Monotype Monotype
	deriving (Eq, Show)

data Expr
	= Var String
	| Appl Expr Expr
	| Lam String Expr
	| Let String Expr Expr
	deriving (Show, Eq)

data Row
	= Row
		{ rIndent :: Int
		, rCtx :: [(String, Type)]
		, rExpr :: TypedExpr
		, rRule :: Int
		}
	deriving (Show, Eq)

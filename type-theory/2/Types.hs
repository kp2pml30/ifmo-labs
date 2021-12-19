module Types where

-- if this 2 lines do not compile, please, change them...
forallStr = "∀ "
specStr = " ⊑ "

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
	deriving (Eq)

instance Show Type where
	show (MType a) = show a
	show (Forall x t) = forallStr ++ x ++ ". " ++ show t

isMonotype (MType _) = True
isMonotype _ = False

data Monotype
	= Type String
	| Arr Monotype Monotype
	deriving (Eq)

embrace x = "(" ++ x ++ ")"

instance Show Monotype where
	show (Type s) = s
	show (Arr l r) =
		let foo = case l of { Arr _ _ -> embrace ; _ -> id } in
		foo (show l) ++ " -> " ++ show r

data Expr
	= Var String
	| Appl Expr Expr
	| Lam String Expr
	| Let String Expr Expr
	deriving (Eq)

instance Show Expr where
	show (Var s) = s
	show (Lam v b) = "(\\" ++ v ++ ". " ++ show b ++ ")"
	show (Appl l r) =
		let lmap = case l of { Let {} -> embrace ; _ -> id } in
		let rmap = case r of { Var {} -> id ; Lam {} -> id ; _ -> embrace } in
		lmap (show l) ++ " " ++ rmap (show r)
	show (Let v d b) = "let " ++ v ++ " = " ++ show d ++ " in " ++ show b

data Row
	= Row
		{ rIndent :: Int
		, rCtx :: [(String, Type)]
		, rExpr :: TypedExpr
		, rRule :: Int
		}
	deriving (Show, Eq)

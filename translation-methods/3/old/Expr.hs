{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE DeriveFoldable, DeriveFunctor #-}

module Obfuscation.Expr where

class (Show a) => Show' a where
    show' :: a -> String
instance Show' String where show' x = x
instance Show' Char where show' x = [x]
instance (Show a) => Show' a where show' = show

newtype Type = Type String deriving (Eq)

instance Show Type where
	show (Type s) = s ++ " "

data Function a
	= Function Type String [(Type, a)] [Statement a]
	deriving (Eq, Foldable, Functor)

foldMy s =
	foldArgs
	where
		foldArgs [] = ""
		foldArgs [x] = x
		foldArgs (x:t) = x ++ s ++ foldArgs t

instance Show' a => Show (Function a) where
	show (Function r n a b)
		= show r ++ n
		++ "(" ++ foldMy "," (map (\(a, b) -> show a ++ show' b) a) ++ ")"
		++ "{" ++ foldMap show b ++ "}"

data Statement a
	= SExpr (Expr a)
	| Decl Type a (Maybe (Expr a))
	| SIf (Expr a) [Statement a] (Maybe [Statement a])
	| Return (Maybe (Expr a))
	deriving (Eq, Foldable, Functor)

instance Show' a => Show (Statement a) where
	show (SExpr e) = show e ++ ";"
	show (Decl t e m) = show t ++ show' e ++ maybe "" ("="++) (show <$> m) ++ ";"
	show (Return e) = "return" ++ maybe "" (" "++) (show <$> e) ++ ";"
	show (SIf c t e) = "if(" ++ show c ++ "){"++ foldMap show t ++ "}" ++ maybe "" (\x -> "else{"++ x ++ "}") (foldMap show <$> e)

data Expr a
	= EOp String (Expr a) (Expr a)
	| EName a
	| ELiteral String
	| Call (Expr a) [Expr a]
	deriving (Eq, Foldable, Functor)

precendence :: String -> Int
precendence "+" = 0
precendence "-" = 0
precendence "*" = 1
precendence "/" = 1
precendence _ = undefined

embrace x = "(" ++ x ++ ")"

instance Show' a => Show (Expr a) where
	show (EOp o l r) =
		(case l of
			EOp lo _ _ | precendence lo < precendence o -> embrace
			_ -> id) (show l)
		++ o ++
		(case r of
			EOp ro _ _ | precendence o >= precendence ro -> embrace
			_ -> id) (show r)
	show (EName s) = show' s
	show (ELiteral s) = s
	show (Call (EName f) a) = show' f ++ "(" ++ foldMy "," (map show a) ++ ")"
	show (Call f a) = "(" ++ show f ++ ")(" ++ foldMy "," (map show a) ++ ")"

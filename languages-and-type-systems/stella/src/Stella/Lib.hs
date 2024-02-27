module Stella.Lib
	( check
	, ErrorData(..)
	) where

import Control.Applicative
import Control.Monad
import Control.Monad.Except
import Control.Monad.State

import qualified Gen.PrintSyntax as Printer -- ( Print, printTree )

import Data.Either
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.DisjointSet as DisjointSet
import Data.DisjointSet (DisjointSet)

import Stella.Errs
import Gen.AbsSyntax as St

data CheckerState
	= CheckerState
	{ typeVars :: DisjointSet Int
	, globalNames :: Map.Map String TType
	, locals :: Map.Map String TType
	}

scoped :: CheckerMonad a -> CheckerMonad a
scoped m = do
	locs <- gets locals
	m `catchError` \e -> do
		modify $ \s -> s { locals = locs }
		throwError e

emptyCheckerState :: CheckerState
emptyCheckerState = CheckerState DisjointSet.empty Map.empty Map.empty

data ErrorData
	= ErrorData
	{ code :: Err
	, related :: [(String, String)]
	}

data TType
	= TVar Int
	| TNat
	| TBool
	| TUnit
	| TTuple [TType]
	| TFn [TType] TType
	| TList TType
	| TRecord (Map.Map String TType)
	deriving (Eq, Show)

typeCtorId :: TType -> Int
typeCtorId (TVar _) = undefined -- 0
typeCtorId (TNat) = 1
typeCtorId (TBool) = 2
typeCtorId (TUnit) = 3
typeCtorId (TTuple _) = 4
typeCtorId (TFn _ _) = 5
typeCtorId (TList _) = 6
typeCtorId (TRecord _) = 7

isVarType :: TType -> Bool
isVarType (TVar _) = True
isVarType _ = False

isAtomicType :: TType -> Bool
isAtomicType TNat = True
isAtomicType TBool = True
isAtomicType TUnit = True
isAtomicType _ = False

newtype CheckerMonad a
  = CheckerMonad { unCheckerMonad :: StateT CheckerState (Except ErrorData) a }
  deriving newtype (Functor, Applicative, Monad, MonadError ErrorData, MonadState CheckerState)

freshVar :: CheckerMonad TType
freshVar = do
	nextId <- gets $ DisjointSet.values . typeVars
	modify $ \s -> s { typeVars = DisjointSet.insert nextId (typeVars s) }
	pure $ TVar nextId

todo :: String -> CheckerMonad a
todo s = throwError $ ErrorData ERROR_TODO [("not implemented", s)]

unident :: StellaIdent -> String
unident (StellaIdent a) = a

getIdentType :: String -> CheckerMonad TType
getIdentType s = do
	r1 <- gets $ (Map.lookup s).  locals
	case r1 of
		Just a -> pure a
		Nothing -> do
			r2 <- gets $ (Map.lookup s) . globalNames
			case r2 of
				Just a -> pure a
				Nothing -> throwError $ ErrorData ERROR_UNDEFINED_VARIABLE [("name", s)]

unconvType :: St.Type -> CheckerMonad TType
unconvType (TypeFun pars r) =
	TFn <$> forM pars unconvType <*> unconvType r
unconvType TypeBool = pure TBool
unconvType TypeNat = pure TNat
unconvType TypeUnit = pure TUnit
--unconvType (TypeForAll [StellaIdent] Type) =
--unconvType (TypeRec StellaIdent Type) =
--unconvType (TypeSum Type Type) =
unconvType (TypeTuple sub) = TTuple <$> forM sub unconvType
unconvType r@(TypeRecord recs) = do
	lst <- forM recs $ \(ARecordFieldType i t) -> do
		tt <- unconvType t
		pure $ (unident i, tt)
	let mp = Map.fromList lst
	when (Map.size mp /= length lst) $ throwError $ ErrorData ERROR_UNEXPECTED_RECORD_FIELDS [("record type", show r)]
	pure $ TRecord mp
--unconvType (TypeVariant [VariantFieldType]) =
unconvType (TypeList t) = TList <$> unconvType t
--unconvType (TypeTop) =
--unconvType (TypeBottom) =
--unconvType (TypeRef Type) =
--unconvType (TypeVar StellaIdent) =
unconvType x = todo $ "unconvType " ++ show x

scrapDecl :: Decl -> CheckerMonad ()
scrapDecl fn@(DeclFun annots name params retType throwType decls expr) = do
	oldNames <- gets globalNames
	when ((unident name) `Map.member` oldNames) $ do
		throwError $ ErrorData ERROR_MISSING_MAIN [("function", Printer.printTree fn)]
	when (not $ null annots) $ todo "annots"
	when (not $ null decls) $ todo "decls"
	when (throwType /= NoThrowType) $ todo "throw type"
	tParTypes <- forM params $ \(AParamDecl id typ) -> do
		unconvType typ
	tRetType <-
		(case retType of
			NoReturnType -> freshVar
			SomeReturnType t -> unconvType t)
	let typ = TFn tParTypes tRetType
	modify $ \s -> s { globalNames = Map.insert (unident name) typ (globalNames s) }
-- scrapDecl (DeclFunGeneric [Annotation] StellaIdent [StellaIdent] [ParamDecl] ReturnType ThrowType [Decl] Expr)
-- scrapDecl (DeclTypeAlias StellaIdent Type)
-- scrapDecl (DeclExceptionType Type)
-- scrapDecl (DeclExceptionVariant StellaIdent Type)
scrapDecl d = todo $ "scrapDecl " ++ show d

unexpectedTypeBy :: TType -> Err
unexpectedTypeBy (TTuple _) = ERROR_UNEXPECTED_TUPLE
unexpectedTypeBy (TList _) = ERROR_UNEXPECTED_LIST
unexpectedTypeBy (TFn _ _) = ERROR_UNEXPECTED_LAMBDA
unexpectedTypeBy (TRecord _) = ERROR_UNEXPECTED_RECORD
unexpectedTypeBy _ = ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION

unifyVarWith :: Int -> TType -> CheckerMonad TType
unifyVarWith var t = todo "unify tvar"

unify :: TType -> TType -> CheckerMonad TType
unify x y | x == y = pure x
-- unify x y | isAtomicType x && isAtomicType y || isAtomicType x /= isAtomicType y = throwError $ ErrorData (unexpectedTypeBy y) [("expected", show x), ("got", show y)]
unify (TTuple a) (TTuple b) = do
	when (length a /= length b) $ throwError $ ErrorData ERROR_UNEXPECTED_TUPLE_LENGTH [("x", show a), ("y", show b)]
	TTuple <$> forM (zip a b) (uncurry unify)
unify (TRecord a) (TRecord b) = do
	when (Map.size a > Map.size b) $ throwError $ ErrorData ERROR_MISSING_RECORD_FIELDS [("x", show a), ("y", show b)]
	when (Map.size a < Map.size b) $ throwError $ ErrorData ERROR_UNEXPECTED_RECORD_FIELDS [("x", show a), ("y", show b)]
	l <- forM (zip (Map.toAscList a) (Map.toAscList b)) $ \((an, at), (bn, bt)) -> do
		when (an /= bn) $ throwError $ ErrorData ERROR_MISSING_RECORD_FIELDS [("x", show a), ("y", show b)]
		rt <- unify at bt
		pure $ (an, rt)
	pure $ TRecord $ Map.fromList l
unify x@(TFn apars aret) y@(TFn bpars bret) = do
	when (length apars /= length bpars) $ throwError $ ErrorData ERROR_UNEXPECTED_TYPE_FOR_PARAMETER [("x", show x), ("y", show y)]
	truePars <- forM (zip apars bpars) (uncurry unify) `catchError`
		\(ErrorData _ c) -> throwError $ ErrorData ERROR_UNEXPECTED_TYPE_FOR_PARAMETER (c ++ [("fn1", show x), ("fn2", show y)])
	trueRet <- unify aret bret
	pure $ TFn truePars trueRet
unify (TVar x) (TVar y) = todo $ "unify vars " ++ show x ++ " vs " ++ show y
unify (TVar x) y = unifyVarWith x y
unify x (TVar y) = unifyVarWith y x
unify x y | typeCtorId x /= typeCtorId y = throwError $ ErrorData (unexpectedTypeBy y) [("expected", show x), ("got", show y)]
unify x y = todo $ "unify " ++ show x ++ " vs " ++ show y

patternFromExprType :: Pattern -> TType -> CheckerMonad (Map.Map String TType)
patternFromExprType (PatternVar v) typ = do
	pure $ Map.fromList [(unident v, typ)]
patternFromExprType x t = todo $ "patternFromExprType " ++ show x ++ " " ++ show t

checkExpr :: St.Expr -> CheckerMonad TType
checkExpr (Succ e) = do
	checkExpr e >>= unify TNat
checkExpr (LogicNot e) = do
	checkExpr e >>= unify TBool
checkExpr (Pred e) = do
	checkExpr e >>= unify TNat
checkExpr (IsZero e) = do
	void $ checkExpr e >>= unify TNat
	pure TBool
checkExpr (ConstTrue) = pure TBool
checkExpr (ConstFalse) = pure TBool
checkExpr (ConstUnit) = pure TUnit
checkExpr (ConstInt _) = pure TNat
checkExpr (Var s) = getIdentType $ unident s
checkExpr (Tuple exprs) = TTuple <$> forM exprs checkExpr
checkExpr (Sequence l r) = do
	_ <- checkExpr l
	checkExpr r
checkExpr (If c t f) = do
	checkExpr c >>= unify TBool
	tt <- checkExpr t
	tf <- checkExpr f
	unify tt tf
checkExpr dt@(DotTuple e i) = do
	tupType <- checkExpr e
	case tupType of
		TTuple els -> do
			when (i <= 0 || i > (toInteger $ length els)) $ throwError $ ErrorData ERROR_TUPLE_INDEX_OUT_OF_BOUNDS [("at", show dt)]
			pure $ els !! ((fromInteger i) - 1)
		_ -> throwError $ ErrorData ERROR_NOT_A_TUPLE [("at", show dt)]
checkExpr app@(Application f args) = do
	fType <- checkExpr f
	case fType of
		TFn params ret -> do
			when (length args /= length params) $ do
				throwError $ ErrorData ERROR_UNEXPECTED_TYPE_FOR_PARAMETER [("at", show app)]
			checekdArgs <- forM args checkExpr
			forM_ (zip params checekdArgs) (uncurry unify) `catchError` \(ErrorData _ c) -> throwError $ ErrorData ERROR_UNEXPECTED_TYPE_FOR_PARAMETER (c ++ [("call", show app)])
			pure ret
		_ -> throwError $ ErrorData ERROR_NOT_A_FUNCTION [("at", show app)]
checkExpr (Let bindings inExpr) = do
	newVars <- forM bindings $ \(APatternBinding pat exp) -> do
		expT <- checkExpr exp
		patternFromExprType pat expT
	scoped $ do
		modify $ \s -> s { locals = List.foldl' Map.union (locals s) newVars }
		checkExpr inExpr
checkExpr (List []) = do
	TList <$> freshVar
checkExpr (List (x:xs)) = do
	t <- checkExpr x
	rest <- forM xs checkExpr
	ty <- foldM (\a b -> unify a b) t rest
	pure $ TList ty
checkExpr (Head l) = do
	lType <- checkExpr l
	case lType of
		TList o -> pure o
		_ -> throwError $ ErrorData ERROR_NOT_A_LIST [("at", show l)]
checkExpr (IsEmpty l) = do
	lType <- checkExpr l
	case lType of
		TList o -> pure TBool
		_ -> throwError $ ErrorData ERROR_NOT_A_LIST [("at", show l)]
checkExpr (Tail l) = do
	lType <- checkExpr l
	case lType of
		TList o -> pure lType
		_ -> throwError $ ErrorData ERROR_NOT_A_LIST [("at", show l)]
checkExpr (ConsList l r) = do
	lt <- checkExpr l
	lr <- checkExpr r
	unify (TList lt) lr
checkExpr (Abstraction params expr) = do
	let paramNames = (\(AParamDecl i _) -> unident i) <$> params
	pars <- forM params $ \(AParamDecl i t) -> do
		tt <- unconvType t
		pure $ (unident i, tt)
	scoped $ do
		modify $ \s -> s { locals = Map.union (Map.fromList pars) (locals s) }
		re <- checkExpr expr
		pure (TFn (snd <$> pars) re)
checkExpr p@(DotRecord r i) = do
	rType <- checkExpr r
	case rType of
		TRecord o ->
			case Map.lookup (unident i) o of
				Nothing -> throwError $ ErrorData ERROR_MISSING_RECORD_FIELDS [("at", show p)]
				Just a -> pure a
		_ -> throwError $ ErrorData ERROR_NOT_A_RECORD [("at", show p)]
checkExpr ex@(Record binds) = do
	typ <- forM binds $ \(ABinding i e) -> do
		et <- checkExpr e
		pure (unident i, et)
	let mp = Map.fromList typ
	when (Map.size mp /= length typ) $ throwError $ ErrorData ERROR_UNEXPECTED_RECORD_FIELDS [("expression", show ex)]
	pure $ TRecord mp
checkExpr x = todo $ "checkExpr " ++ show x
-- checkExpr (Assign Expr Expr)
-- checkExpr (LetRec [PatternBinding] Expr)
-- checkExpr (TypeAbstraction [StellaIdent] Expr)
-- checkExpr (LessThan Expr Expr)
-- checkExpr (LessThanOrEqual Expr Expr)
-- checkExpr (GreaterThan Expr Expr)
-- checkExpr (GreaterThanOrEqual Expr Expr)
-- checkExpr (Equal Expr Expr)
-- checkExpr (NotEqual Expr Expr)
-- checkExpr (TypeAsc Expr Type)
-- checkExpr (TypeCast Expr Type)
-- checkExpr (Variant StellaIdent ExprData)
-- checkExpr (Match Expr [MatchCase])
-- checkExpr (Add Expr Expr)
-- checkExpr (Subtract Expr Expr)
-- checkExpr (LogicOr Expr Expr)
-- checkExpr (Multiply Expr Expr)
-- checkExpr (Divide Expr Expr)
-- checkExpr (LogicAnd Expr Expr)
-- checkExpr (Ref Expr)
-- checkExpr (Deref Expr)
-- checkExpr (TypeApplication Expr [Type])
-- checkExpr (Panic)
-- checkExpr (Throw Expr)
-- checkExpr (TryCatch Expr Pattern Expr)
-- checkExpr (TryWith Expr Expr)
-- checkExpr (Inl Expr)
-- checkExpr (Inr Expr)
-- checkExpr (Fix Expr)
-- checkExpr (NatRec Expr Expr Expr)
-- checkExpr (Fold Type Expr)
-- checkExpr (Unfold Type Expr)
-- checkExpr (ConstMemory MemoryAddress)

checkDecl :: Decl -> CheckerMonad ()
checkDecl fn@(DeclFun annots name params retType throwType decls expr) = do
	when (not $ null annots) $ todo "annots"
	when (not $ null decls) $ todo "decls"
	when (throwType /= NoThrowType) $ todo "throw type"
	(parsTyp, retTyp) <- (gets $ (Map.! (unident name)) . globalNames) >>= \case
		(TFn parsTyp retTyp) -> pure (parsTyp, retTyp)
		_ -> undefined
	let paramNames = (\(AParamDecl i _) -> unident i) <$> params
	scoped $ do
		modify $ \s -> s { locals = Map.fromList (zip paramNames parsTyp) }
		re <- checkExpr expr
		_ <- unify retTyp re
		pure ()
-- checkDecl (DeclFunGeneric [Annotation] StellaIdent [StellaIdent] [ParamDecl] ReturnType ThrowType [Decl] Expr)
-- checkDecl (DeclTypeAlias StellaIdent Type)
-- checkDecl (DeclExceptionType Type)
-- checkDecl (DeclExceptionVariant StellaIdent Type)
checkDecl d = todo $ "checkDecl " ++ show d

doCheck :: Program -> CheckerMonad ()
doCheck (AProgram _ _ decls) = do
	forM_ decls scrapDecl
	forM_ decls checkDecl

check :: Program -> [ErrorData]
check p = either (:[]) (const []) $ runExcept $ evalStateT (unCheckerMonad $ doCheck p) emptyCheckerState

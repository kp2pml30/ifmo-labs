module Stella.Lib
	( check
	, ErrorData(..)
	) where

import Control.Applicative
import Control.Monad
import Control.Monad.Except
import Control.Monad.State

import System.IO.Unsafe (unsafePerformIO)

import Data.Either
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.DisjointSet as DisjointSet
import Data.DisjointSet (DisjointSet)

import qualified Gen.PrintSyntax as Printer -- ( Print, printTree )

import Stella.Errs
import Gen.AbsSyntax as St

data VarConstraint = IsTuple | IsRecord deriving (Eq, Show)

data CheckerState
	= CheckerState
	{ typeVars :: DisjointSet Int
	, knownVars :: Map.Map Int (Either [VarConstraint] TType)
	, globalNames :: Map.Map String TType
	, locals :: Map.Map String TType
	}

scoped :: CheckerMonad a -> CheckerMonad a
scoped m = do
	locs <- gets locals
	let fin = modify $ \s -> s { locals = locs }
	(m <* fin) `catchError` \e -> do
		fin
		throwError e

emptyCheckerState :: CheckerState
emptyCheckerState = CheckerState DisjointSet.empty Map.empty Map.empty Map.empty

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
	| TSum TType TType
	| TVariant (Map.Map String TType)
	| TUnit1
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
typeCtorId (TSum _ _) = 8
typeCtorId (TVariant _) = 9
typeCtorId TUnit1 = 10

isVarType :: TType -> Bool
isVarType (TVar _) = True
isVarType _ = False

newtype CheckerMonad a
  = CheckerMonad { unCheckerMonad :: StateT CheckerState (Except ErrorData) a }
  deriving newtype (Functor, Applicative, Monad, MonadError ErrorData, MonadState CheckerState)

freshVarId :: CheckerMonad Int
freshVarId = do
	nextId <- gets $ DisjointSet.values . typeVars
	modify $ \s -> s { typeVars = DisjointSet.insert nextId (typeVars s) }
	pure nextId

freshVar :: CheckerMonad TType
freshVar = TVar <$> freshVarId

todo :: String -> CheckerMonad a
todo s = throwError $ ErrorData ERROR_TODO [("not implemented", s)]

unident :: StellaIdent -> String
unident (StellaIdent a) = a

getIdentType :: String -> CheckerMonad TType
getIdentType s = do
	r1 <- gets $ (Map.lookup s) . locals
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
unconvType (TypeSum l r) =
	TSum <$> unconvType l <*> unconvType r
unconvType (TypeTuple sub) = TTuple <$> forM sub unconvType
unconvType r@(TypeRecord recs) = do
	lst <- forM recs $ \(ARecordFieldType i t) -> do
		tt <- unconvType t
		pure $ (unident i, tt)
	let mp = Map.fromList lst
	when (Map.size mp /= length lst) $ throwError $ ErrorData ERROR_UNEXPECTED_RECORD_FIELDS [("record type", show r)]
	pure $ TRecord mp
unconvType (TypeVariant vars) = do
	vr <- forM vars $ \(AVariantFieldType i ot) -> do
		tp <- (case ot of
			NoTyping -> pure $ TUnit1
			SomeTyping o -> unconvType o)
		pure (unident i, tp)
	pure $ TVariant $ Map.fromList vr
unconvType (TypeList t) = TList <$> unconvType t
--unconvType (TypeTop) =
--unconvType (TypeBottom) =
--unconvType (TypeRef Type) =
--unconvType (TypeVar StellaIdent) =
unconvType x = todo $ "unconvType " ++ show x

scrapDecl :: String -> Decl -> CheckerMonad ()
scrapDecl pref fn@(DeclFun annots name params retType throwType decls expr) = do
	oldNames <- gets globalNames
	let realName = pref ++ unident name
	when (realName `Map.member` oldNames) $ do
		throwError $ ErrorData ERROR_MISSING_MAIN [("function", Printer.printTree fn)]
	when (not $ null annots) $ todo "annots"
	-- forM_ decls $ scrapDecl (realName ++ "::")
	when (throwType /= NoThrowType) $ todo "throw type"
	tParTypes <- forM params $ \(AParamDecl _ typ) -> do
		unconvType typ
	tRetType <-
		(case retType of
			NoReturnType -> pure TUnit
			SomeReturnType t -> unconvType t)
	let typ = TFn tParTypes tRetType
	modify $ \s -> s { globalNames = Map.insert realName typ (globalNames s) }
-- scrapDecl (DeclFunGeneric [Annotation] StellaIdent [StellaIdent] [ParamDecl] ReturnType ThrowType [Decl] Expr)
-- scrapDecl (DeclTypeAlias StellaIdent Type)
-- scrapDecl (DeclExceptionType Type)
-- scrapDecl (DeclExceptionVariant StellaIdent Type)
scrapDecl _ d = todo $ "scrapDecl " ++ show d

unexpectedTypeBy :: TType -> TType -> Err
unexpectedTypeBy _ (TTuple _) = ERROR_UNEXPECTED_TUPLE
unexpectedTypeBy _ (TList _) = ERROR_UNEXPECTED_LIST
unexpectedTypeBy _ (TFn _ _) = ERROR_UNEXPECTED_LAMBDA
unexpectedTypeBy _ (TRecord _) = ERROR_UNEXPECTED_RECORD
unexpectedTypeBy _ (TSum _ _) = ERROR_UNEXPECTED_INJECTION
unexpectedTypeBy _ (TVariant _) = ERROR_UNEXPECTED_VARIANT
unexpectedTypeBy (TFn _ _) _ = ERROR_NOT_A_FUNCTION
unexpectedTypeBy (TTuple _) _ = ERROR_NOT_A_TUPLE
unexpectedTypeBy (TRecord _) _ = ERROR_NOT_A_RECORD
unexpectedTypeBy (TList _) _ = ERROR_NOT_A_LIST
unexpectedTypeBy _ _ = ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION

getVarRepr :: Int -> CheckerMonad Int
getVarRepr v = do
	tv <- gets typeVars
	let res = (DisjointSet.representative' v tv)
	let v' = maybe v id (fst res)
	modify $ \s -> s { typeVars = snd res }
	pure $ v'

unifyVarWith :: Bool -> Int -> TType -> CheckerMonad TType
unifyVarWith shouldFlip var t = do
	t <- getActualType t
	let uni = if shouldFlip then flip unify else unify
	var' <- getVarRepr var
	kw <- gets knownVars
	case Map.lookup var' kw of
		Nothing -> do
			modify $ \s -> s { knownVars = Map.insert var' (Right t) (knownVars s) }
			pure t
		Just (Right t') -> do
			rt <- uni t' t
			modify $ \s -> s { knownVars = Map.insert var' (Right rt) (knownVars s) }
			pure rt
		Just (Left cons) -> do
			forM_ cons $ \case
				IsTuple ->
					case t of
						TTuple _ -> pure ()
						_ -> throwError $ ErrorData ERROR_NOT_A_TUPLE [("type", show t)]
				IsRecord ->
					case t of
						TRecord _ -> pure ()
						_ -> throwError $ ErrorData ERROR_NOT_A_RECORD [("type", show t)]
			modify $ \s -> s { knownVars = Map.insert var' (Right t) (knownVars s) }
			pure t

getActualType :: TType -> CheckerMonad TType
getActualType (TVar t) = do
	t' <- getVarRepr t
	kw <- gets knownVars
	case Map.lookup t' kw of
		Just (Right t) -> pure t
		_ -> pure $ TVar t'
getActualType (TTuple sub) = TTuple <$> forM sub getActualType
getActualType (TFn args ret) = TFn <$> forM args getActualType <*> getActualType ret
getActualType (TList el) = TList <$> getActualType el
getActualType (TRecord mp) = do
	TRecord . Map.fromList <$> forM (Map.toList mp) (\(f, s) -> (f,) <$> getActualType s)
getActualType (TSum l r) = TSum <$> getActualType l <*> getActualType r
getActualType (TVariant mp) = do
	TVariant . Map.fromList <$> forM (Map.toList mp) (\(f, s) -> (f,) <$> getActualType s)
getActualType a = pure a

hasVar :: TType -> Bool
hasVar (TVar t) = True
hasVar (TTuple sub) = any hasVar sub
hasVar (TFn args ret) = hasVar ret || any hasVar args
hasVar (TList el) = hasVar el
hasVar (TRecord mp) = any hasVar $ snd <$> Map.toList mp
hasVar (TSum l r) = hasVar l || hasVar r
hasVar (TVariant mp) = any hasVar $ snd <$> Map.toList mp
hasVar a = False

unify :: TType -> TType -> CheckerMonad TType
unify x y | x == y = pure x
unify TUnit1 _ = throwError $ ErrorData ERROR_UNEXPECTED_DATA_FOR_NULLARY_LABEL []
unify _ TUnit1 = throwError $ ErrorData ERROR_MISSING_DATA_FOR_LABEL []
unify (TVar x) (TVar y) = do
	x' <- getVarRepr x
	y' <- getVarRepr y
	tv <- gets typeVars
	kw <- gets knownVars
	case (Map.lookup x' kw, Map.lookup y' kw) of
		(Nothing, Nothing) -> do
			modify $ \s -> s { typeVars = DisjointSet.union x' y' tv }
			pure $ TVar x'
		(Just a, Nothing) -> do
			modify $ \s -> s { typeVars = DisjointSet.union x' y' tv, knownVars = Map.insert y' a kw }
			pure $ either (const $ TVar x') id a
		(Nothing, Just a) -> do
			modify $ \s -> s { typeVars = DisjointSet.union x' y' tv, knownVars = Map.insert x' a kw }
			pure $ either (const $ TVar y') id a
		(Just (Right a), Just (Right b)) -> do
			rt <- unify a b
			modify $ \s -> s { typeVars = DisjointSet.union x' y' tv, knownVars = Map.insert x' (Right rt) (Map.insert y' (Right rt) (knownVars s)) }
			pure rt
		(Just (Left a), Just (Left b)) -> do
			let res = (Left $ a ++ b)
			modify $ \s -> s { typeVars = DisjointSet.union x' y' tv, knownVars = Map.insert x' res (Map.insert y' res (knownVars s)) }
			pure $ TVar x'
		(Just (Left a), Just (Right b)) ->
			unifyVarWith False x b
		(Just (Right a), Just (Left b)) -> do
			unifyVarWith True y a
unify (TVar x) y = unifyVarWith False x y
unify x (TVar y) = unifyVarWith True y x
unify x y | typeCtorId x /= typeCtorId y =
	case x of
		TFn _ _ -> throwError $ ErrorData ERROR_NOT_A_FUNCTION [("expected", show x), ("got", show y)]
		_ -> throwError $ ErrorData (unexpectedTypeBy x y) [("expected", show x), ("got", show y)]
unify (TTuple a) (TTuple b) = do
	when (length a /= length b) $ throwError $ ErrorData ERROR_UNEXPECTED_TUPLE_LENGTH [("x", show a), ("y", show b)]
	TTuple <$> forM (zip a b) (uncurry unify)
unify (TList a) (TList b) = do
	TList <$> unify a b
unify (TRecord a) (TRecord b) = do
	when (Map.size a > Map.size b) $ throwError $ ErrorData ERROR_MISSING_RECORD_FIELDS [("x", show a), ("y", show b)]
	when (Map.size a < Map.size b) $ throwError $ ErrorData ERROR_UNEXPECTED_RECORD_FIELDS [("x", show a), ("y", show b)]
	l <- forM (zip (Map.toAscList a) (Map.toAscList b)) $ \((an, at), (bn, bt)) -> do
		when (an /= bn) $ throwError $ ErrorData ERROR_MISSING_RECORD_FIELDS [("x", show a), ("y", show b)]
		rt <- unify at bt
		pure $ (an, rt)
	pure $ TRecord $ Map.fromList l
unify x@(TFn apars aret) y@(TFn bpars bret) = do
	when (length apars /= length bpars) $ throwError $ ErrorData ERROR_INCORRECT_NUMBER_OF_ARGUMENTS [("x", show x), ("y", show y)]
	truePars <- forM (zip apars bpars) (uncurry unify) `catchError`
		\(ErrorData _ c) -> throwError $ ErrorData ERROR_UNEXPECTED_TYPE_FOR_PARAMETER (c ++ [("fn1", show x), ("fn2", show y)])
	trueRet <- unify aret bret
	pure $ TFn truePars trueRet
unify (TSum al ar) (TSum bl br) = do
	rl <- unify al bl
	rr <- unify ar br
	pure $ TSum rl rr
unify (TVariant x) (TVariant y) = do
	let inter = Map.intersection y x
	when (Map.size inter /= Map.size y) $ throwError $ ErrorData ERROR_UNEXPECTED_VARIANT_LABEL [("x", show x), ("y", show y)]
	forM_ (Map.toList inter) $ \(n, v) -> do
		void $ unify (x Map.! n) v
	pure (TVariant x)
unify x y = todo $ "unify " ++ show x ++ " vs " ++ show y

patternFromExprType :: Pattern -> TType -> CheckerMonad (Map.Map String TType)
patternFromExprType (PatternVar v) typ = do
	pure $ Map.fromList [(unident v, typ)]
patternFromExprType x t = todo $ "patternFromExprType " ++ show x ++ " " ++ show t

data CoveredCases
	= CoveredTrue
	| CoveredFalse
	| CoveredAll
	| CoveredSum CoveredCases CoveredCases
	| CoveredVariant (Map.Map String CoveredCases)
	| CoveredNone
	| CoveredNat (Set.Set Int) (Maybe Int) -- ints, min var
	| CoveredTuple [CoveredCases]
	| CoveredRecord (Map.Map String CoveredCases)
	| CoveredList Bool CoveredCases CoveredCases
	deriving (Eq, Show)

mergeCoveredCases :: CoveredCases -> CoveredCases -> CheckerMonad CoveredCases
CoveredNone `mergeCoveredCases` a = pure a
a `mergeCoveredCases` CoveredNone = pure a
CoveredFalse `mergeCoveredCases` CoveredTrue = pure CoveredAll
CoveredTrue `mergeCoveredCases` CoveredFalse = pure CoveredAll
CoveredAll `mergeCoveredCases` _ = pure CoveredAll
_ `mergeCoveredCases` CoveredAll = pure CoveredAll
CoveredTuple a `mergeCoveredCases` CoveredTuple b = do
	sub <- forM (zip a b) $ uncurry mergeCoveredCases
	if all (== CoveredAll) sub
	then pure CoveredAll
	else pure $ CoveredTuple sub
CoveredNat a b `mergeCoveredCases` CoveredNat x y = do
	let
		minVar =
			case (b, y) of
				(Nothing, Nothing) -> Nothing
				(Just a, Nothing) -> Just a
				(Nothing, Just b) -> Just b
				(Just a, Just b) -> Just $ a `min` b
	let ints = Set.union a x
	case minVar of
		Nothing -> pure $ CoveredNat ints Nothing
		Just minVar ->
			if Set.size (Set.filter (\x -> x < minVar && x >= 0) ints) == minVar
			then pure $ CoveredAll
			else pure $ CoveredNat ints (Just minVar)
(CoveredSum al ar) `mergeCoveredCases` (CoveredSum bl br) = do
	rl <- mergeCoveredCases al bl
	rr <- mergeCoveredCases ar br
	case (rl, rr) of
		(CoveredAll, CoveredAll) -> pure CoveredAll
		_ -> pure $ CoveredSum rl rr
CoveredVariant lv `mergeCoveredCases` CoveredVariant rv = do
	let common = Map.keys $ Map.intersection lv rv
	com <- forM common $ \k -> (k,) <$> mergeCoveredCases (lv Map.! k) (rv Map.! k)
	let res = (Map.fromList com) `Map.union` (lv Map.\\ rv) `Map.union` (rv Map.\\ lv)
	if all (== CoveredAll) $ snd <$> Map.toList res
	then pure CoveredAll
	else pure $ CoveredVariant res
CoveredRecord l `mergeCoveredCases` CoveredRecord r = do
	let int = Map.intersection l r
	int' <- forM (Map.toList int) $ \(k, v) -> do
		(k,) <$> (r Map.! k) `mergeCoveredCases` v
	let re = Map.union (l Map.\\ int) (Map.union (r Map.\\ int) $ Map.fromList int')
	if all (== CoveredAll) re
	then pure CoveredAll
	else pure $ CoveredRecord re
CoveredList n1 h1 t1 `mergeCoveredCases` CoveredList n2 h2 t2 = do
	let nr = n1 || n2
	hr <- h1 `mergeCoveredCases` h2
	tr <- t1 `mergeCoveredCases` t2
	if nr && hr == CoveredAll && tr == CoveredAll
	then pure $ CoveredAll
	else pure $ CoveredList nr hr tr
l `mergeCoveredCases` r | l == r = pure l
l `mergeCoveredCases` r = todo $ "mergeCoveredCases " ++ show l ++ " " ++ show r

unifyInMatch :: TType -> TType -> CheckerMonad ()
unifyInMatch exp got = do
	(void $ unify exp got) `catchError` \case
		(ErrorData ERROR_UNEXPECTED_DATA_FOR_NULLARY_LABEL ctx) -> throwError $ ErrorData ERROR_UNEXPECTED_NON_NULLARY_VARIANT_PATTERN ctx
		(ErrorData ERROR_MISSING_DATA_FOR_LABEL ctx) -> throwError $ ErrorData ERROR_UNEXPECTED_NULLARY_VARIANT_PATTERN ctx
		(ErrorData _ ctx) ->
			throwError $ ErrorData ERROR_UNEXPECTED_PATTERN_FOR_TYPE $
				ctx ++ [("exp", show exp), ("got", show got)]

checkMatch :: TType ->Pattern -> CheckerMonad CoveredCases
checkMatch scruType (PatternVar vn) = do
	modify $ \s -> s { locals = Map.insert (unident vn) scruType (locals s) }
	pure CoveredAll
checkMatch scruType PatternFalse = do
	unifyInMatch TBool scruType
	pure CoveredFalse
checkMatch scruType PatternTrue = do
	unifyInMatch TBool scruType
	pure CoveredTrue
checkMatch scruType (PatternInl r) = do
	lt <- freshVar
	rt <- freshVar
	unifyInMatch (TSum lt rt) scruType
	CoveredSum <$> checkMatch lt r <*> pure CoveredNone
checkMatch scruType (PatternInr r) = do
	lt <- freshVar
	rt <- freshVar
	unifyInMatch (TSum lt rt) scruType
	CoveredSum CoveredNone <$> checkMatch rt r
checkMatch scruType PatternUnit = do
	unifyInMatch TUnit scruType
	pure CoveredAll
checkMatch scruType (PatternVariant i NoPatternData) = do
	st <- getActualType scruType
	unifyInMatch scruType (TVariant $ Map.fromList [(unident i, TUnit1)]) `catchError` \(ErrorData _ ctx) ->
		throwError $ ErrorData ERROR_UNEXPECTED_NULLARY_VARIANT_PATTERN ctx
	pure $ CoveredVariant $ Map.fromList [(unident i, CoveredAll)]
checkMatch scruType (PatternVariant i (SomePatternData v)) = do
	fv <- freshVar
	unifyInMatch scruType (TVariant $ Map.fromList [(unident i, fv)])
	caseTyp <- getActualType fv
	when (caseTyp == TUnit1) $ throwError $ ErrorData ERROR_UNEXPECTED_NON_NULLARY_VARIANT_PATTERN []
	m <- checkMatch fv v
	pure $ CoveredVariant $ Map.fromList [(unident i, m)]
checkMatch scruType (PatternInt i) = do
	unifyInMatch (TNat) scruType
	pure $ CoveredNat (Set.fromList [fromInteger i]) Nothing
checkMatch scruType pat@(PatternSucc _) = do
	unifyInMatch (TNat) scruType
	spinPatNat 0 pat
	where
		spinPatNat :: Int -> Pattern -> CheckerMonad CoveredCases
		spinPatNat n (PatternSucc sc) = spinPatNat (n + 1) sc
		spinPatNat n (PatternInt i) = pure $ CoveredNat (Set.fromList [fromInteger i + n]) Nothing
		spinPatNat n (PatternVar vn) = do
			modify $ \s -> s { locals = Map.insert (unident vn) TNat (locals s) }
			pure $ CoveredNat Set.empty $ Just n
		spinPatNat _ pt = todo $ "spinPatNat " ++ show pat
checkMatch scruType (PatternTuple pats) = do
	patTup <- forM pats $ \_ -> freshVar
	unifyInMatch scruType $ TTuple patTup
	CoveredTuple <$> forM (zip patTup pats) (uncurry checkMatch)
checkMatch scruType (PatternRecord pats) = do
	patRec <- forM pats $ \(ALabelledPattern id _) -> (unident id,) <$> freshVar
	void $ unify scruType $ TRecord $ Map.fromList patRec
	CoveredRecord . Map.fromList <$> (forM (zip patRec pats) $ \((_, var), ALabelledPattern id pat) -> do
		(unident id,)<$> checkMatch var pat)
checkMatch scruType (PatternCons h t) = do
	fv <- freshVar
	unifyInMatch scruType $ TList fv
	CoveredList False <$> checkMatch fv h <*> checkMatch (TList fv) t
checkMatch scruType (PatternList lst) = do
	fv <- freshVar
	unifyInMatch scruType $ TList fv
	List.foldr
		(\li bk -> do
			he <- checkMatch fv li
			b <- bk
			pure $ CoveredList False he b)
		(pure $ CoveredList True CoveredNone CoveredNone)
		lst
checkMatch _ pat = todo $ "checkMatch " ++ show pat

checkTotality :: TType -> CoveredCases -> CheckerMonad ()
checkTotality _ CoveredAll = pure ()
checkTotality t CoveredNone = throwError $ ErrorData ERROR_ILLEGAL_EMPTY_MATCHING [("for type", show t)]
checkTotality t c = throwError $ ErrorData ERROR_NONEXHAUSTIVE_MATCH_PATTERNS [("for type", show t), ("covered", show c)]

checkExpr :: TType -> St.Expr -> CheckerMonad ()
checkExpr expType (Succ e) = do
	_ <- unify TNat expType
	checkExpr TNat e
checkExpr expType (LogicNot e) = do
	_ <- unify TBool expType
	checkExpr TBool e
checkExpr expType (Pred e) = do
	_ <- unify TNat expType
	checkExpr TNat e
checkExpr expType (IsZero e) = do
	_ <- unify TBool expType
	checkExpr TNat e
checkExpr expType (ConstTrue) = void $ unify expType TBool
checkExpr expType (ConstFalse) = void $ unify expType TBool
checkExpr expType (ConstUnit) = void $ unify expType TUnit
checkExpr expType (ConstInt _) = void $ unify expType TNat
checkExpr expType (Var s) = do
	r <- getIdentType $ unident s
	void $ unify expType r
checkExpr expType (Tuple exprs) = do
	tupTypes <- forM exprs $ const freshVar
	void $ unify expType (TTuple tupTypes)
	forM_ (zip tupTypes exprs) (uncurry checkExpr)
checkExpr expType (Sequence l r) = do
	checkExpr TUnit l
	checkExpr expType r
checkExpr expType (If c t f) = do
	checkExpr TBool c
	checkExpr expType t
	checkExpr expType f
checkExpr expType app@(Application f args) = do
	argTypes <- forM args (const freshVar)
	checkExpr (TFn argTypes expType) f `catchError` \case
		ErrorData ERROR_UNEXPECTED_NUMBER_OF_PARAMETERS_IN_LAMBDA ctx -> throwError $ ErrorData ERROR_INCORRECT_NUMBER_OF_ARGUMENTS ctx
		x -> throwError x
	forM_ (zip argTypes args) (uncurry checkExpr)
checkExpr expType (Let bindings inExpr) = do
	newVars <- forM bindings $ \(APatternBinding pat exp) -> do
		fv <- freshVar
		checkExpr fv exp
		patternFromExprType pat fv
	scoped $ do
		modify $ \s -> s { locals = List.foldl' Map.union (locals s) newVars }
		checkExpr expType inExpr
checkExpr expType l@(List []) = do
	tVar <- freshVar
	res <- unify expType (TList tVar)
	getActualType tVar >>= \a -> when (hasVar a) $ throwError $ ErrorData ERROR_AMBIGUOUS_LIST [("list", show l)]
checkExpr expType (List all) = do
	tVar <- freshVar
	void $ unify expType (TList tVar)
	forM_ all (checkExpr tVar)
checkExpr expType (Head l) = do
	checkExpr (TList expType) l
checkExpr expType (IsEmpty l) = do
	_ <- unify TBool expType
	tVar <- freshVar
	checkExpr (TList tVar) l
checkExpr expType (Tail l) = do
	fv <- freshVar
	void $ unify (expType) (TList fv)
	checkExpr expType l
checkExpr expType (ConsList l r) = do
	tVar <- freshVar
	_ <- unify expType (TList tVar)
	checkExpr tVar l
	checkExpr expType r
checkExpr expType (Abstraction params expr) = do
	rt <- freshVar
	pars <- forM params $ \(AParamDecl i t) -> do
		tt <- unconvType t
		pure $ (unident i, tt)
	(void $ unify expType $ TFn (snd <$> pars) rt) `catchError` \rethrow@(ErrorData e ctx) -> do
		when (e == ERROR_INCORRECT_NUMBER_OF_ARGUMENTS) $ throwError $ ErrorData ERROR_UNEXPECTED_NUMBER_OF_PARAMETERS_IN_LAMBDA ctx
		throwError rethrow
	scoped $ do
		modify $ \s -> s { locals = Map.union (Map.fromList pars) (locals s) }
		checkExpr rt expr
checkExpr expType dt@(DotTuple e i) = do
	fv <- freshVarId
	modify $ \s -> s { knownVars = Map.insert fv (Left [IsTuple]) (knownVars s) }
	checkExpr (TVar fv) e
	tupType <- getActualType (TVar fv)
	case tupType of
		TTuple els -> do
			when (i <= 0 || i > (toInteger $ length els)) $ throwError $ ErrorData ERROR_TUPLE_INDEX_OUT_OF_BOUNDS [("at", show dt)]
			void $ unify expType (els !! (fromInteger i - 1))
		detType -> throwError $ ErrorData ERROR_NOT_A_TUPLE [("at", show dt), ("detecteed type", show detType)]
checkExpr expType p@(DotRecord r i) = do
	fv <- freshVarId
	modify $ \s -> s { knownVars = Map.insert fv (Left [IsRecord]) (knownVars s) }
	checkExpr (TVar fv) r
	rType <- getActualType (TVar fv)
	case rType of
		TRecord o ->
			case Map.lookup (unident i) o of
				Nothing -> throwError $ ErrorData ERROR_UNEXPECTED_FIELD_ACCESS [("at", show p)]
				Just a -> void $ unify expType a
		_ -> throwError $ ErrorData ERROR_NOT_A_RECORD [("at", show p)]
checkExpr expType ex@(Record binds) = do
	bindVars <- Map.fromList <$> forM binds (\(ABinding i _) -> (unident i,) <$> freshVar)
	void $ unify expType (TRecord bindVars)
	forM_ binds $ \(ABinding i e) -> do
		checkExpr (bindVars Map.! (unident i)) e
checkExpr expType (Inl e) = do
	lt <- freshVar
	rt <- freshVar
	void $ unify expType (TSum lt rt)
	checkExpr lt e
checkExpr expType (Inr e) = do
	lt <- freshVar
	rt <- freshVar
	void $ unify expType (TSum lt rt)
	checkExpr rt e
checkExpr expType (NatRec cnt init fn) = do
	checkExpr TNat cnt
	checkExpr expType init
	checkExpr (TFn [TNat] $ TFn [expType] expType) fn
checkExpr expType (TypeAsc e t) = do
	et <- unconvType t
	void $ unify expType et
	checkExpr et e
checkExpr expType (Variant i NoExprData) = do
	let res = TVariant $ Map.fromList [(unident i, TUnit1)]
	void $ unify expType res
checkExpr expType (Variant i (SomeExprData e)) = do
	fv <- freshVar
	checkExpr fv e
	void (unify expType (TVariant $ Map.fromList [(unident i, fv)]))
	-- prnt <- getActualType fv
	--let !_ = unsafePerformIO $ putStrLn $ show fv ++ " <- " ++ show prnt ++ " exp " ++ show expType
	--void (unify expType (TVariant $ Map.fromList [(unident i, fv)])) `catchError` \(ErrorData err ctx) -> do
	--	when (err == )
	--	throwError $ ErrorData ERROR_UNEXPECTED_DATA_FOR_NULLARY_LABEL ctx
checkExpr expType (Fix e) =
	checkExpr (TFn [expType] expType) e
checkExpr expType (Match scrutinee cases) = do
	fv <- freshVar
	checkExpr fv scrutinee
	real <- getActualType fv
	let !_ = unsafePerformIO $ print real
	let cm = checkMatch fv
	let
		ff a (AMatchCase p e) = do
			scoped $ do
				b <- cm p
				checkExpr expType e
				mergeCoveredCases a b
	let
		startCov =
			case real of
				TVariant v -> CoveredVariant $ const CoveredNone <$> v
				_ -> CoveredNone
	covRes <- foldM ff startCov cases
	let !_ = unsafePerformIO $ print covRes
	covRes <- covRes `mergeCoveredCases` covRes
	let !_ = unsafePerformIO $ print covRes
	checkTotality fv covRes
checkExpr expType x = todo $ "checkExpr " ++ show x ++ " expected " ++ show expType
-- checkExpr (Assign Expr Expr)
-- checkExpr (LetRec [PatternBinding] Expr)
-- checkExpr (TypeAbstraction [StellaIdent] Expr)
-- checkExpr (LessThan Expr Expr)
-- checkExpr (LessThanOrEqual Expr Expr)
-- checkExpr (GreaterThan Expr Expr)
-- checkExpr (GreaterThanOrEqual Expr Expr)
-- checkExpr (Equal Expr Expr)
-- checkExpr (NotEqual Expr Expr)
-- checkExpr (TypeCast Expr Type)
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
-- checkExpr (Fold Type Expr)
-- checkExpr (Unfold Type Expr)
-- checkExpr (ConstMemory MemoryAddress)

checkDecl :: String -> Decl -> CheckerMonad (String, TType)
checkDecl pref (DeclFun annots name params _ throwType decls expr) = do
	let realName = pref ++ unident name
	when (not $ null annots) $ todo "annots"
	when (throwType /= NoThrowType) $ todo "throw type"
	(parsTyp, retTyp) <- (gets $ (Map.! realName) . globalNames) >>= \case
		(TFn parsTyp retTyp) -> pure (parsTyp, retTyp)
		_ -> undefined
	let paramNames = (\(AParamDecl i _) -> unident i) <$> params
	scoped $ do
		modify $ \s -> s { locals = Map.fromList (zip paramNames parsTyp) `Map.union` locals s }
		forM_ decls $ \d -> do
			scrapDecl (realName ++ "::") d
			(n, t) <- checkDecl (realName ++ "::") d
			modify $ \s -> s { locals = Map.insert n t $ locals s }
		checkExpr retTyp expr
	pure (unident name, TFn parsTyp retTyp)
-- checkDecl (DeclFunGeneric [Annotation] StellaIdent [StellaIdent] [ParamDecl] ReturnType ThrowType [Decl] Expr)
-- checkDecl (DeclTypeAlias StellaIdent Type)
-- checkDecl (DeclExceptionType Type)
-- checkDecl (DeclExceptionVariant StellaIdent Type)
checkDecl _ d = todo $ "checkDecl " ++ show d

doCheck :: Program -> CheckerMonad ()
doCheck (AProgram _ _ decls) = do
	forM_ decls $ scrapDecl ""
	gd <- gets globalNames
	case Map.lookup "main" gd of
		Just (TFn [_] _) -> pure ()
		Just (TFn _ _) -> throwError $ ErrorData ERROR_INCORRECT_ARITY_OF_MAIN []
		_ -> throwError $ ErrorData ERROR_MISSING_MAIN []
	forM_ decls $ void . checkDecl ""

check :: Program -> [ErrorData]
check p = either (:[]) (const []) $ runExcept $ evalStateT (unCheckerMonad $ doCheck p) emptyCheckerState

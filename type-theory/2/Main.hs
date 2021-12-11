{-# LANGUAGE DerivingStrategies, GeneralizedNewtypeDeriving, TupleSections #-}

module Main (main) where

import Par
import Lex
import Types

import System.IO (hPutStrLn, stderr)

import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Trans.Except
import Control.Monad.Except
import Control.Monad.Extra
import qualified Data.List.Extra
import qualified Data.Map as Map

data CheckerState
	= CheckerState
		{ csIndent :: !Int
		, csLine :: !Int
		, csLinesStack :: [Int]
		, csRest :: [Row]
		}
	deriving (Eq, Show)

data CheckerExc
	= CheckerExc
		{ ceMsg :: String
		, ceCause :: Maybe CheckerExc
		, ceLine :: !Int
		}
	deriving (Eq, Show)

newtype CheckerM a
	= CheckerM (ExceptT CheckerExc (StateT CheckerState Identity) a)
	deriving newtype (Functor, Monad, Applicative, MonadState CheckerState, MonadError CheckerExc)

runCheckerM (CheckerM m) state = runIdentity $ flip runStateT state $ runExceptT m

throwChecker :: (Int -> CheckerExc) -> CheckerM a
throwChecker err = gets (head . csLinesStack) >>= throwError . err

throwCheckerFast :: String -> CheckerM a
throwCheckerFast s = throwChecker $ CheckerExc s Nothing

nop :: Monad m => m ()
nop = return ()

fetchRow :: CheckerM Row
fetchRow = do
	state@CheckerState {..} <- get
	when (null csRest) (throwCheckerFast "unexpected eof")
	let hd = head csRest
	when (rIndent hd /= csIndent) (throwCheckerFast $ "wrong indent\nexpected " <> show csIndent <> "\n got " <> show (rIndent hd))
	put state { csRest = tail csRest, csLine = csLine + 1 }
	return hd

pushIndent :: CheckerM ()
pushIndent = modify \s@CheckerState {..} -> s { csIndent = csIndent + 1, csLinesStack = csLine:csLinesStack }
popIndent :: CheckerM ()
popIndent = modify \s@CheckerState {..} -> s { csIndent = csIndent - 1, csLinesStack = tail csLinesStack }

data Proofed = Proofed { pCtx :: ![(String, Type)], pExpr :: !TypedExpr } deriving (Eq, Show)

checkRule1 :: Proofed -> CheckerM ()
checkRule1 Proofed { pCtx, pExpr = TypedExpr exp typ } = do
	case exp of
		Var s -> do
			let asPair = (s, typ)
			when (asPair `notElem` pCtx) $ throwCheckerFast "not presented in context"
		_ -> throwCheckerFast "rule 1 expects variable"

checkRule2 :: Proofed -> CheckerM ()
checkRule2 Proofed { pCtx = ctxm, pExpr = TypedExpr exprm typem } = do
	Proofed { pCtx = ctx0, pExpr = TypedExpr expr0 type0 } <- checkSubtree
	Proofed { pCtx = ctx1, pExpr = TypedExpr expr1 type1 } <- checkSubtree
	unless (Data.List.Extra.allSame [ctxm, ctx0, ctx1]) $ throwCheckerFast "context mismatch"
	when (exprm /= Appl expr0 expr1) $ throwCheckerFast "wrong rule, expected application"
	case type0 of
		MType (Arr tau tau') -> do
			when (type1 /= MType tau) $ throwCheckerFast "function application type mismatch (tau argument)"
			when (typem /= MType tau') $ throwCheckerFast "function application type mismatch (tau' result)"
		_ -> throwCheckerFast "expected `->` type in first subtree"

checkRule3 :: Proofed -> CheckerM ()
checkRule3 Proofed { pCtx = ctxm, pExpr = TypedExpr exprm typem } = do
	Proofed { pCtx = ctx0, pExpr = TypedExpr e tau' } <- checkSubtree
	when (null ctx0) $ throwCheckerFast "expected non-empty context"
	let ((x, tau):ctxt) = ctx0
	when (ctxt /= ctxm) $ throwCheckerFast "context mismatch"
	case exprm of
		Lam xC eC -> do
			when (x /= xC) $ throwCheckerFast $ "argument mismatch `" ++ x ++ "` != `" ++ xC ++ "`"
			when (e /= eC) $ throwCheckerFast "body mismatch"
		_ -> throwCheckerFast "wrong rule (by expression)"
	case typem of
		MType (Arr tauC tauC') | tau == MType tauC && tau' == MType tauC' -> nop
		_ -> throwCheckerFast "wrong rule (by type)"

checkRule4 :: Proofed -> CheckerM ()
checkRule4 Proofed { pCtx = ctxm, pExpr = TypedExpr exprm typem } = do
	Proofed { pCtx = ctx0, pExpr = TypedExpr e0 sigma } <- checkSubtree
	Proofed { pCtx = ctx1, pExpr = TypedExpr e1 tau } <- checkSubtree
	unless (isMonotype tau) $ throwCheckerFast "tau must be a monotype"
	when (null ctx1) $ throwCheckerFast "second subtree context must be non-empty"
	let ((x, sigmaC):ctx1') = ctx1
	unless (Data.List.Extra.allSame [ctxm, ctx0, ctx1']) $ throwCheckerFast "context mismatch"
	when (sigma /= sigmaC) $ throwCheckerFast "type mismatch between variable and declaration-expression (sigma)"
	case exprm of
		Let xC e0C e1C -> do
			when (x /= xC) $ throwCheckerFast $ "varname mismatch : `" ++ x ++ "` != `" ++ xC ++ "`"
			when (e0 /= e0C) $ throwCheckerFast "let part mismatch (e0)"
			when (e1 /= e1C) $ throwCheckerFast "in part mismatch (e1)"
		_ -> throwCheckerFast "wrong rule"

breakType :: Type -> ([String], Monotype)
breakType = helper []
	where
		helper :: [String] -> Type -> ([String], Monotype)
		helper !accum (MType a) = (accum, a)
		helper !accum (Forall v t) = helper (v : accum) t

isNotFree :: String -> Type -> Bool
isNotFree var (Forall var' expr) =
	var == var' || var `isNotFree` expr
isNotFree var (MType mono) = isNotFree' mono
	where
		isNotFree' :: Monotype -> Bool
		isNotFree' (Type t) = var /= t
		isNotFree' (Arr l r) = isNotFree' l && isNotFree' r

isSpecialization :: Type -> Type -> Bool
isSpecialization l r =
	let (lvars, ltype) = breakType l in
	let (rvars, rtype) = breakType r in
	all (`isNotFree` l) rvars
		&& evalState (fitTo ltype rtype) (Map.fromList $ map (, Nothing) lvars)
	where
		fitTo :: Monotype -> Monotype -> State (Map.Map String (Maybe Monotype)) Bool
		fitTo (Type alpha) r = do
			m <- gets $ Map.lookup alpha
			case m of
				-- it is not a replacable var
				Nothing -> return $ Type alpha == r
				-- var is not assigned
				Just Nothing -> do
					modify $ Map.insert alpha (Just r)
					return True
				-- var known
				Just (Just a) -> return $ a == r
		fitTo (Arr l1 l2) (Arr r1 r2) = do
			-- liftM2 (&&) (fitTo l1 r1) (fitTo l2 r2)
			rl <- fitTo l1 r1
			if rl
			then fitTo l2 r2
			else return False
		fitTo _ _ = return False

checkRule5 :: Proofed -> CheckerM ()
checkRule5 Proofed {..} = do
	Proofed { pCtx = uCtx, pExpr = uExpr } <- checkSubtree
	when (pCtx /= uCtx) $ throwCheckerFast "context mismatch"
	let TypedExpr me mt = pExpr
	let TypedExpr ue ut = uExpr
	when (me /= ue) $ throwCheckerFast "expressions are not equal"
	unless (ut `isSpecialization` mt) $ throwCheckerFast "types are not related by specialization"

checkRule6 :: Proofed -> CheckerM ()
checkRule6 Proofed {..} = do
	Proofed { pCtx = uCtx, pExpr = uExpr } <- checkSubtree
	when (pCtx /= uCtx) $ throwCheckerFast "context mismatch"
	case pExpr of
		TypedExpr e (Forall alpha sigma) -> do
			case uExpr of
				TypedExpr e' sigma' | e == e' && sigma == sigma' -> nop
				_ -> throwCheckerFast "wrong subtree"
			unless (all (\(v, t) -> v /= alpha && alpha `isNotFree` t) pCtx) $ throwCheckerFast $ "`" ++ alpha ++ "` is a free vairable"
		_ -> throwCheckerFast "wrong rule"

checkSubtree :: CheckerM Proofed
checkSubtree = do
	Row {..} <- fetchRow
	let proofed = Proofed (reverse rCtx) rExpr
	pushIndent
	case rRule of
		1 -> checkRule1 proofed
		2 -> checkRule2 proofed
		3 -> checkRule3 proofed
		4 -> checkRule4 proofed
		5 -> checkRule5 proofed
		6 -> checkRule6 proofed
		_ -> throwChecker $ CheckerExc ("unknown rule " <> show rRule) Nothing
	popIndent
	return proofed

checkWhole :: CheckerM ()
checkWhole = do
	void checkSubtree
	whenM (gets $ not . null . csRest) $ throwChecker $ CheckerExc "unreachable proof" Nothing

main = do
	s <- getContents
	let toks = TIndent 0 : alexScanTokens s
	let parsed = parse toks
	case fst $ runCheckerM checkWhole $ CheckerState 0 0 [-1] parsed of
		Right () -> putStrLn "Correct"
		Left CheckerExc {..} -> do
			putStrLn "Incorrect"
			hPutStrLn stderr $ ceMsg <> " at line " <> show ceLine
			case ceCause of
				Just a -> hPutStrLn stderr $ "\tcaused by " <> show a
				_ -> nop

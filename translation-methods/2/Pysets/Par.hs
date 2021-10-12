module Pysets.Par (ParserError(..), parse) where

import Pysets.Tokens
import Pysets.Expr

import Data.List (foldl', find)
import Data.Maybe
import Control.Monad.State
import Control.Monad
import Control.Monad.Extra
import Control.Monad.Trans.Except
import Control.Monad.Except (throwError)
import Control.Monad.Identity

type MyState = [Token]
type MyMonadT e m r = StateT MyState (ExceptT e m) r

runMyMonadT :: (Monad m) => MyMonadT e m a -> MyState -> m (Either e a)
runMyMonadT m = runExceptT . evalStateT m

type MyMonad e a = MyMonadT e Identity a
runMyMonad m = runIdentity . runMyMonadT m

newtype ParserError = ParserError String deriving (Show, Eq, Ord)

type PMonad a = MyMonad ParserError a

parse :: [Token] -> Either ParserError Expr
parse = runMyMonad parseFinish

lhas :: PMonad Bool
lhas = gets (not . null)

lpeek :: PMonad Token
lpeek = gets head

ltrypeek :: PMonad (Maybe Token)
ltrypeek = ifM lhas (Just <$> lpeek) (return Nothing)

lfetch :: PMonad Token
lfetch = do
	ret <- gets head
	modify tail
	return ret

lfetchIf :: (Token -> Bool) -> PMonad (Maybe Token)
lfetchIf f = do
	res <- find f <$> ltrypeek
	when (isJust res) (void lfetch)
	return res

mkError s = lgetPos >>= lift . throwError . ParserError . (\x -> s ++ " at " ++ x)

lassert :: (Token -> Bool) -> String -> PMonad Token
lassert f s =
	lfetchIf f >>= maybe (mkError s) return

lgetPos :: PMonad String
lgetPos = maybe "<EOF>" (show . position) <$> ltrypeek

parseFinish :: PMonad Expr
parseFinish = do
	res <- parseM
	whenM (gets (not . null)) (mkError "unparsed end")
	return res

parseM :: PMonad Expr
parseM = parseIn

parseAnd = makeBop isTAnd And parseAtom
parseXor = makeBop isTXor Xor parseAnd
parseOr  = makeBop isTOr  Or  parseXor
parseIn  = makeBopEx
	(seqFoldFirst (lfetchIf isTIn) checkNotIn)
	(\l r p -> Not (In l r p) p)
	parseOr

checkNotIn = lfetchIf isTNot >>= mapM \not' -> lassert isTIn ("missing `in` in `not in` operator")

makeBopEx :: PMonad (Maybe Token) -> (Expr -> Expr -> Position -> Expr) -> PMonad Expr -> PMonad Expr
makeBopEx checker returner lower = lower >>= spin
	where
		spin :: Expr -> PMonad Expr
		spin l = do
			op <- checker
			comb <- mapM (cont l . position) op
			maybe (return l) spin comb
		cont :: Expr -> Position -> PMonad Expr
		cont l op = do
			r <- lower
			return $ returner l r op

makeBop checker = makeBopEx (lfetchIf checker)

parseAtom :: PMonad Expr
parseAtom = do
	result <- foldl' seqFoldFirst (return Nothing) [tryName, tryParen]
	maybe (mkError "can't parse atom at ") return result
	where
		tryParen :: PMonad (Maybe Expr)
		tryParen = do
			got <- lfetchIf isTLParen
			mapM (const $ do
					res <- parseM
					_ <- lassert isTRParen "expected )"
					return res)
				got
		tryName :: PMonad (Maybe Expr)
		tryName = lfetchIf isTName >>= mapM (\TName{..} -> return $ Name tName tPos)


seqFoldFirst :: PMonad (Maybe a) -> PMonad (Maybe a) -> PMonad (Maybe a)
seqFoldFirst a b = do
	res <- a
	maybe b (const $ return res) res

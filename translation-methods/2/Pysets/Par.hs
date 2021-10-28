module Pysets.Par (ParserError(..), parse) where

import Pysets.Tokens
import Pysets.Expr
import Pysets.Exc

import Data.List (foldl', find)
import Data.Maybe
import Control.Monad
import Control.Monad.Extra
import Control.Monad.Except (throwError)
import Control.Monad.State

type MyState = TokenList
type PMonad a = PysetsMonad MyState a

parse :: TokenList -> Either ParserError Expr
parse = runPysetsMonad parseFinish

lhas :: PMonad Bool
lhas = do
	g <- get
	return $ case g of
		ListEof -> False
		_       -> True


lpeekMod :: (Token -> TokenList -> PMonad ()) -> PMonad Token
lpeekMod mod = do
	l <- get
	case l of
		ListEof -> error "error in parser"
		TokenListCons h t -> mod h t >> return h
		ListError err -> throwError err

lpeek :: PMonad Token
lpeek = lpeekMod (\_ _ -> return ())

ltrypeek :: PMonad (Maybe Token)
ltrypeek = ifM lhas (Just <$> lpeek) (return Nothing)

lfetch :: PMonad Token
lfetch = lpeekMod (\_ t -> put t)

lfetchIf :: (Token -> Bool) -> PMonad (Maybe Token)
lfetchIf f = do
	res <- find f <$> ltrypeek
	when (isJust res) (void lfetch)
	return res

mkError s = lgetPos >>= lift . throwError . ParserError s

lassert :: (Token -> Bool) -> String -> PMonad Token
lassert f s =
	lfetchIf f >>= maybe (mkError s) return

lgetPos :: PMonad (Maybe Position)
lgetPos = fmap position <$> ltrypeek

parseFinish :: PMonad Expr
parseFinish = do
	res <- parseM
	whenM lhas (mkError "unparsed end")
	return res

parseM :: PMonad Expr
parseM = parseIn

cpos x a b t = x a b (position t)

parseMinus = makeBop isTMinus (cpos Minus) parseAtom
parseAnd = makeBop isTAnd (cpos And) parseMinus
parseXor = makeBop isTXor (cpos Xor) parseAnd
parseOr  = makeBop isTOr  (cpos Or)  parseXor
parseIn  = makeBopEx
	(seqFoldFirst (lfetchIf isTIn) checkNotIn)
	(\l r p ->
		let po = position p in
		case p of
			TNot {} -> Not (In l r po) po
			_       -> In l r po)
	parseOr

checkNotIn = lfetchIf isTNot >>= mapM \not' -> lassert isTIn ("missing `in` in `not in` operator") >> return not'

makeBopEx :: PMonad (Maybe Token) -> (Expr -> Expr -> Token -> Expr) -> PMonad Expr -> PMonad Expr
makeBopEx checker returner lower = lower >>= spin
	where
		spin :: Expr -> PMonad Expr
		spin l = do
			op <- checker
			comb <- mapM (cont l) op
			maybe (return l) spin comb
		cont :: Expr -> Token -> PMonad Expr
		cont l op = do
			r <- lower
			return $ returner l r op

makeBop checker = makeBopEx (lfetchIf checker)

parseAtom :: PMonad Expr
parseAtom = do
	result <- foldl' seqFoldFirst (return Nothing) [tryName, tryParen, tryNot]
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
		tryNot :: PMonad (Maybe Expr)
		tryNot =
			lfetchIf isTNot >>= mapM (\nt -> do
				res <- parseAtom
				return $ Not res (position nt))

seqFoldFirst :: PMonad (Maybe a) -> PMonad (Maybe a) -> PMonad (Maybe a)
seqFoldFirst a b = do
	res <- a
	maybe b (const $ return res) res

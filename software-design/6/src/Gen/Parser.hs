{-# OPTIONS_GHC -w #-}
module Gen.Parser (parse) where

import Data.Maybe
import Tokens
import Ast
{-
 -- first --
ADDSUB
	lpar	0
	num	0
ADDSUB'
		0
	addsub	1
ATOM
	lpar	1
	num	0
EXPR
	lpar	0
	num	0
FILE
	lpar	0
	num	0
MULDIV
	lpar	0
	num	0
MULDIV'
		0
	muldiv	1

 -- follow --
ADDSUB
	
	rpar
ADDSUB'
	
	rpar
ATOM
	
	addsub
	muldiv
	rpar
EXPR
	
	rpar
FILE
	
MULDIV
	
	addsub
	rpar
MULDIV'
	
	addsub
	rpar

-}
import Control.Monad.Identity
import Control.Monad.Except
import Control.Monad.Trans.Except
import Control.Monad.State
import Yada.ParGen.Runtime

data YGTerminal
  = YGTAddsub
  | YGTLpar
  | YGTMuldiv
  | YGTNum
  | YGTRpar
  | YGTEof
  deriving (Eq, Ord, Show, Enum)

type YGMonad a = StateT (TokensList (Token a, YGTerminal)) (ExceptT LexError Identity)

mapTok :: Token a -> YGTerminal
mapTok tok = case tok of
  TLpar -> YGTLpar
  TRpar -> YGTRpar
  TNum a -> YGTNum
  TOp op | op == Add || op == Sub -> YGTAddsub
  TOp op | op == Mul || op == Div -> YGTMuldiv

fbreaklpar = breaklpar <$> fetchTerm
breaklpar (pos, tok) = case tok of
  TLpar -> ()
fbreakrpar = breakrpar <$> fetchTerm
breakrpar (pos, tok) = case tok of
  TRpar -> ()
fbreaknum = breaknum <$> fetchTerm
breaknum (pos, tok) = case tok of
  TNum a ->  ANum a
fbreakaddsub = breakaddsub <$> fetchTerm
breakaddsub (pos, tok) = case tok of
  TOp op | op == Add || op == Sub ->  \l r -> AOp l op r
fbreakmuldiv = breakmuldiv <$> fetchTerm
breakmuldiv (pos, tok) = case tok of
  TOp op | op == Mul || op == Div ->  \l r -> AOp l op r

parseFILE :: YGMonad a (Ast a)
parseFILE = do
  peek <- peekTerm
  case peek of
    YGTLpar -> make0
    YGTNum -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `FILE` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = (id) <$> parseEXPR
parseEXPR = do
  peek <- peekTerm
  case peek of
    YGTLpar -> make0
    YGTNum -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `EXPR` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = (id) <$> parseADDSUB
parseADDSUB = do
  peek <- peekTerm
  case peek of
    YGTLpar -> make0
    YGTNum -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `ADDSUB` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = (\l o -> o l) <$> parseMULDIV <*> parseADDSUB'
parseADDSUB' = do
  peek <- peekTerm
  case peek of
    YGTAddsub -> make1
    YGTRpar -> make0
    YGTEof -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `ADDSUB'` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = (id) <$ return ()
    make1 = (\o r u l -> u (o l r)) <$> fbreakaddsub <*> parseMULDIV <*> parseADDSUB'
parseMULDIV = do
  peek <- peekTerm
  case peek of
    YGTLpar -> make0
    YGTNum -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `MULDIV` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = (\l o -> o l) <$> parseATOM <*> parseMULDIV'
parseMULDIV' = do
  peek <- peekTerm
  case peek of
    YGTMuldiv -> make1
    YGTAddsub -> make0
    YGTRpar -> make0
    YGTEof -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `MULDIV'` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = (id) <$ return ()
    make1 = (\o r u l -> u (o l r)) <$> fbreakmuldiv <*> parseATOM <*> parseMULDIV'
parseATOM = do
  peek <- peekTerm
  case peek of
    YGTLpar -> make1
    YGTNum -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `ATOM` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = (id) <$> fbreaknum
    make1 = (\_ e _ -> e) <$> fbreaklpar <*> parseEXPR <*> fbreakrpar

peekTerm :: YGMonad a YGTerminal
peekTerm = do
  peek <- get
  case peek of
    TLError a -> throwError a
    TLEof _ -> return YGTEof
    TLCons a _ _ -> return $ snd a

peekPos :: YGMonad a Position
peekPos = do
  peek <- get
  case peek of
    TLError a -> throwError a
    TLEof p -> return p
    TLCons _ p _ -> return p

fetchTerm :: YGMonad a (Position, Token a)
fetchTerm = do
  peek <- get
  case peek of
    TLError a -> throwError a
    TLEof p -> return (p, undefined)
    TLCons a p t -> do
      put t
      return (p, fst a)

ensureEof :: YGMonad a ()
ensureEof = peekTerm >>= \p -> case p of
    YGTEof -> return ()
    _ -> peekPos >>= \pos -> throwError $ LexError ("expected Eof got " <> show p) pos 

parse :: TokensList (Token a) -> Either LexError (Ast a)
parse = runIdentity . runExceptT . evalStateT (parseFILE <* ensureEof) . ((\x -> (x, mapTok x)) <$>)

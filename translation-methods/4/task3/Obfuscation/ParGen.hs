{-# OPTIONS_GHC -w #-}
module Obfuscation.ParGen (parse) where
import Obfuscation.Tokens
import Control.Monad
import Obfuscation.Tokens
import Obfuscation.Obf
{-
 -- first --
ADDSUB
	literal	0
	lpar	0
	name	0
ADDSUB'
		0
	addsub	1
ARG
	type	0
ARGS
	type	0
ARGS'
		0
	comma	1
ARGSCOMMA
	comma	0
ASTERISCS
		0
	mul	1
ATOM
	literal	1
	lpar	2
	name	0
BODY
		0
	if	1
	literal	1
	lpar	1
	name	1
	return	1
	type	2
	while	1
CALL
	literal	0
	lpar	0
	name	0
CALLARGS
	literal	0
	lpar	0
	name	0
CALLARGS'
		0
	comma	1
CALLARGSCOMMA
	comma	0
DECL
	type	0
ELSE
		0
	else	1
EXPR
	literal	0
	lpar	0
	name	0
FILE
		0
	type	1
FUNC
	type	0
MBARGS
		0
	type	1
MBCALL
		0
	lpar	1
MBCALLARGS
		0
	literal	1
	lpar	1
	name	1
MBEXPR
		0
	literal	1
	lpar	1
	name	1
MULDIV
	literal	0
	lpar	0
	name	0
MULDIV'
		0
	div	1
	mul	1
MULDIVOP
	div	1
	mul	0
STATEMENT
	if	2
	literal	0
	lpar	0
	name	0
	return	1
	while	3
TYPE
	type	0

 -- follow --
ADDSUB
	comma
	rpar
	scol
ADDSUB'
	comma
	rpar
	scol
ARG
	comma
	rpar
ARGS
	rpar
ARGS'
	rpar
ARGSCOMMA
	type
ASTERISCS
	name
ATOM
	addsub
	comma
	div
	lpar
	mul
	rpar
	scol
BODY
	rcpar
CALL
	addsub
	comma
	div
	mul
	rpar
	scol
CALLARGS
	rpar
CALLARGS'
	rpar
CALLARGSCOMMA
	literal
	lpar
	name
DECL
	if
	literal
	lpar
	name
	rcpar
	return
	type
	while
ELSE
	if
	literal
	lpar
	name
	rcpar
	return
	type
	while
EXPR
	comma
	rpar
	scol
FILE
	
FUNC
	
	type
MBARGS
	rpar
MBCALL
	addsub
	comma
	div
	mul
	rpar
	scol
MBCALLARGS
	rpar
MBEXPR
	scol
MULDIV
	addsub
	comma
	rpar
	scol
MULDIV'
	addsub
	comma
	rpar
	scol
MULDIVOP
	literal
	lpar
	name
STATEMENT
	if
	literal
	lpar
	name
	rcpar
	return
	type
	while
TYPE
	name

-}
import Control.Monad.Identity
import Control.Monad.Except
import Control.Monad.Trans.Except
import Control.Monad.State
import YLex.Lex (TokensList(..))
import YLex.Base (LexError(..), Position)

data YGTerminal
  = YGTAddsub
  | YGTComma
  | YGTDiv
  | YGTElse
  | YGTIf
  | YGTLcpar
  | YGTLiteral
  | YGTLpar
  | YGTMul
  | YGTName
  | YGTRcpar
  | YGTReturn
  | YGTRpar
  | YGTScol
  | YGTSet
  | YGTType
  | YGTWhile
  | YGTEof
  deriving (Eq, Ord, Show, Enum)

type YGTok = Token
type YGFile = [Md]
type YGMonad = StateT (TokensList (YGTok, YGTerminal)) (ExceptT LexError Identity)

mapTok :: YGTok -> YGTerminal
mapTok tok = case tok of
  TName "int" -> YGTType
  TName "char" -> YGTType
  TName "void" -> YGTType
  TName "return" -> YGTReturn
  TName "while" -> YGTWhile
  TName "if" -> YGTIf
  TName "else" -> YGTElse
  TName y -> YGTName
  TLiteral y -> YGTLiteral
  TSet -> YGTSet
  TLParen -> YGTLpar
  TRParen -> YGTRpar
  TLCParen -> YGTLcpar
  TRCParen -> YGTRcpar
  TComma -> YGTComma
  TSColon -> YGTScol
  TAdd -> YGTAddsub
  TSub -> YGTAddsub
  TMul -> YGTMul
  TDiv -> YGTDiv

breaktype (pos, tok@(TName "int")) = "int"
breaktype (pos, tok@(TName "char")) = "char"
breaktype (pos, tok@(TName "void")) = "void"
breakreturn (pos, tok@(TName "return")) = ()
breakwhile (pos, tok@(TName "while")) = ()
breakif (pos, tok@(TName "if")) = ()
breakelse (pos, tok@(TName "else")) = ()
breakname (pos, tok@(TName y)) = y
breakliteral (pos, tok@(TLiteral y)) = y
breakset (pos, tok@(TSet)) = ()
breaklpar (pos, tok@(TLParen)) = ()
breakrpar (pos, tok@(TRParen)) = ()
breaklcpar (pos, tok@(TLCParen)) = ()
breakrcpar (pos, tok@(TRCParen)) = ()
breakcomma (pos, tok@(TComma)) = ()
breakscol (pos, tok@(TSColon)) = ()
breakaddsub (pos, tok@(TAdd)) = bopLift "+"
breakaddsub (pos, tok@(TSub)) = bopLift "-"
breakmul (pos, tok@(TMul)) = ()
breakdiv (pos, tok@(TDiv)) = ()

parseFILE :: YGMonad YGFile
parseFILE = do
  peek <- peekTerm
  case peek of
    YGTType -> make1
    YGTEof -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `FILE` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = do
      return $ ([])
    make1 = do
      v0 <- parseFUNC
      v1 <- parseFILE
      return $ ((:)) v0 v1
parseFUNC = do
  peek <- peekTerm
  case peek of
    YGTType -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `FUNC` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = do
      v0 <- parseTYPE
      v1 <- breakname <$> fetchTerm
      v2 <- breaklpar <$> fetchTerm
      v3 <- parseMBARGS
      v4 <- breakrpar <$> fetchTerm
      v5 <- breaklcpar <$> fetchTerm
      v6 <- parseBODY
      v7 <- breakrcpar <$> fetchTerm
      return $ (\t n _ args _ _ body _ -> mkFunc (t ++ " " ++ n) args (rndAction body)) v0 v1 v2 v3 v4 v5 v6 v7
parseTYPE = do
  peek <- peekTerm
  case peek of
    YGTType -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `TYPE` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = do
      v0 <- breaktype <$> fetchTerm
      v1 <- parseASTERISCS
      return $ ((++)) v0 v1
parseASTERISCS = do
  peek <- peekTerm
  case peek of
    YGTMul -> make1
    YGTName -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `ASTERISCS` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = do
      return $ ("")
    make1 = do
      v0 <- breakmul <$> fetchTerm
      v1 <- parseASTERISCS
      return $ (\_ -> ('*':)) v0 v1
parseMBARGS = do
  peek <- peekTerm
  case peek of
    YGTType -> make1
    YGTRpar -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `MBARGS` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = do
      return $ ([])
    make1 = do
      v0 <- parseARGS
      return $ (id) v0
parseARGS = do
  peek <- peekTerm
  case peek of
    YGTType -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `ARGS` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = do
      v0 <- parseARG
      v1 <- parseARGS'
      return $ (\l o -> o l) v0 v1
parseARGS' = do
  peek <- peekTerm
  case peek of
    YGTComma -> make1
    YGTRpar -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `ARGS'` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = do
      return $ ((\x -> [x] :: [(String, String)]))
    make1 = do
      v0 <- parseARGSCOMMA
      v1 <- parseARG
      v2 <- parseARGS'
      return $ (\o r u l -> o l (u r)) v0 v1 v2
parseARGSCOMMA = do
  peek <- peekTerm
  case peek of
    YGTComma -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `ARGSCOMMA` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = do
      v0 <- breakcomma <$> fetchTerm
      return $ (const (:)) v0
parseARG = do
  peek <- peekTerm
  case peek of
    YGTType -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `ARG` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = do
      v0 <- parseTYPE
      v1 <- breakname <$> fetchTerm
      return $ (\t n -> (t, n) :: (String, String)) v0 v1
parseBODY = do
  peek <- peekTerm
  case peek of
    YGTIf -> make1
    YGTLiteral -> make1
    YGTLpar -> make1
    YGTName -> make1
    YGTReturn -> make1
    YGTType -> make2
    YGTWhile -> make1
    YGTRcpar -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `BODY` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = do
      return $ (rndAction (return ""))
    make1 = do
      v0 <- parseSTATEMENT
      v1 <- parseBODY
      return $ (\s b -> rndAction $ liftM2 (++) s b) v0 v1
    make2 = do
      v0 <- parseDECL
      v1 <- parseBODY
      return $ (\d b -> rndAction $ bodyDecl d b) v0 v1
parseDECL = do
  peek <- peekTerm
  case peek of
    YGTType -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `DECL` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = do
      v0 <- breaktype <$> fetchTerm
      v1 <- breakname <$> fetchTerm
      v2 <- breakset <$> fetchTerm
      v3 <- parseEXPR
      v4 <- breakscol <$> fetchTerm
      return $ (\t n _ e _ -> (t, n, e)) v0 v1 v2 v3 v4
parseSTATEMENT = do
  peek <- peekTerm
  case peek of
    YGTIf -> make2
    YGTLiteral -> make0
    YGTLpar -> make0
    YGTName -> make0
    YGTReturn -> make1
    YGTWhile -> make3
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `STATEMENT` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = do
      v0 <- parseEXPR
      v1 <- breakscol <$> fetchTerm
      return $ (\e _ -> (++ ";") <$> e) v0 v1
    make1 = do
      v0 <- breakreturn <$> fetchTerm
      v1 <- parseMBEXPR
      v2 <- breakscol <$> fetchTerm
      return $ (\_ e _ -> (\x -> "return " ++ x ++ ";") <$> e) v0 v1 v2
    make2 = do
      v0 <- breakif <$> fetchTerm
      v1 <- breaklpar <$> fetchTerm
      v2 <- parseEXPR
      v3 <- breakrpar <$> fetchTerm
      v4 <- breaklcpar <$> fetchTerm
      v5 <- parseBODY
      v6 <- breakrcpar <$> fetchTerm
      v7 <- parseELSE
      return $ (\_ _ c _ _ b _ e -> mkIf c b e) v0 v1 v2 v3 v4 v5 v6 v7
    make3 = do
      v0 <- breakwhile <$> fetchTerm
      v1 <- breaklpar <$> fetchTerm
      v2 <- parseEXPR
      v3 <- breakrpar <$> fetchTerm
      v4 <- breaklcpar <$> fetchTerm
      v5 <- parseBODY
      v6 <- breakrcpar <$> fetchTerm
      return $ (\_ _ c _ _ b _ -> mkWhile c b) v0 v1 v2 v3 v4 v5 v6
parseMBEXPR = do
  peek <- peekTerm
  case peek of
    YGTLiteral -> make1
    YGTLpar -> make1
    YGTName -> make1
    YGTScol -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `MBEXPR` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = do
      return $ (return "" :: Md)
    make1 = do
      v0 <- parseEXPR
      return $ (id) v0
parseELSE = do
  peek <- peekTerm
  case peek of
    YGTElse -> make1
    YGTIf -> make0
    YGTLiteral -> make0
    YGTLpar -> make0
    YGTName -> make0
    YGTRcpar -> make0
    YGTReturn -> make0
    YGTType -> make0
    YGTWhile -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `ELSE` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = do
      return $ (return "" :: Md)
    make1 = do
      v0 <- breakelse <$> fetchTerm
      v1 <- breaklcpar <$> fetchTerm
      v2 <- parseBODY
      v3 <- breakrcpar <$> fetchTerm
      return $ (\_ _ b _ -> (\x -> "else{" ++ x ++ "}") <$> b) v0 v1 v2 v3
parseEXPR = do
  peek <- peekTerm
  case peek of
    YGTLiteral -> make0
    YGTLpar -> make0
    YGTName -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `EXPR` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = do
      v0 <- parseADDSUB
      return $ (id) v0
parseADDSUB = do
  peek <- peekTerm
  case peek of
    YGTLiteral -> make0
    YGTLpar -> make0
    YGTName -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `ADDSUB` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = do
      v0 <- parseMULDIV
      v1 <- parseADDSUB'
      return $ (\l o -> o l) v0 v1
parseADDSUB' = do
  peek <- peekTerm
  case peek of
    YGTAddsub -> make1
    YGTComma -> make0
    YGTRpar -> make0
    YGTScol -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `ADDSUB'` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = do
      return $ (id)
    make1 = do
      v0 <- breakaddsub <$> fetchTerm
      v1 <- parseMULDIV
      v2 <- parseADDSUB'
      return $ (\o r u l -> u (o l r)) v0 v1 v2
parseMULDIV = do
  peek <- peekTerm
  case peek of
    YGTLiteral -> make0
    YGTLpar -> make0
    YGTName -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `MULDIV` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = do
      v0 <- parseCALL
      v1 <- parseMULDIV'
      return $ (\l o -> o l) v0 v1
parseMULDIV' = do
  peek <- peekTerm
  case peek of
    YGTDiv -> make1
    YGTMul -> make1
    YGTAddsub -> make0
    YGTComma -> make0
    YGTRpar -> make0
    YGTScol -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `MULDIV'` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = do
      return $ (id)
    make1 = do
      v0 <- parseMULDIVOP
      v1 <- parseCALL
      v2 <- parseMULDIV'
      return $ (\o r u l -> u (o l r)) v0 v1 v2
parseMULDIVOP = do
  peek <- peekTerm
  case peek of
    YGTDiv -> make1
    YGTMul -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `MULDIVOP` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = do
      v0 <- breakmul <$> fetchTerm
      return $ (const (bopLift "*")) v0
    make1 = do
      v0 <- breakdiv <$> fetchTerm
      return $ (const (bopLift "/")) v0
parseCALL = do
  peek <- peekTerm
  case peek of
    YGTLiteral -> make0
    YGTLpar -> make0
    YGTName -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `CALL` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = do
      v0 <- parseATOM
      v1 <- parseMBCALL
      return $ (liftM2 (++)) v0 v1
parseMBCALL = do
  peek <- peekTerm
  case peek of
    YGTLpar -> make1
    YGTAddsub -> make0
    YGTComma -> make0
    YGTDiv -> make0
    YGTMul -> make0
    YGTRpar -> make0
    YGTScol -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `MBCALL` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = do
      return $ (return "")
    make1 = do
      v0 <- breaklpar <$> fetchTerm
      v1 <- parseMBCALLARGS
      v2 <- breakrpar <$> fetchTerm
      return $ (\_ ca _ -> (\x -> "(" ++ x ++ ")") <$> ca) v0 v1 v2
parseMBCALLARGS = do
  peek <- peekTerm
  case peek of
    YGTLiteral -> make1
    YGTLpar -> make1
    YGTName -> make1
    YGTRpar -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `MBCALLARGS` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = do
      return $ (return "")
    make1 = do
      v0 <- parseCALLARGS
      return $ (id) v0
parseCALLARGS = do
  peek <- peekTerm
  case peek of
    YGTLiteral -> make0
    YGTLpar -> make0
    YGTName -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `CALLARGS` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = do
      v0 <- parseEXPR
      v1 <- parseCALLARGS'
      return $ (\l o -> o l) v0 v1
parseCALLARGS' = do
  peek <- peekTerm
  case peek of
    YGTComma -> make1
    YGTRpar -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `CALLARGS'` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = do
      return $ (id)
    make1 = do
      v0 <- parseCALLARGSCOMMA
      v1 <- parseEXPR
      v2 <- parseCALLARGS'
      return $ (\o r u l -> o l (u r)) v0 v1 v2
parseCALLARGSCOMMA = do
  peek <- peekTerm
  case peek of
    YGTComma -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `CALLARGSCOMMA` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = do
      v0 <- breakcomma <$> fetchTerm
      return $ (const $ bopLift ",") v0
parseATOM = do
  peek <- peekTerm
  case peek of
    YGTLiteral -> make1
    YGTLpar -> make2
    YGTName -> make0
    _ -> peekPos >>= \p -> throwError $ LexError ("can't parse `ATOM` from `" ++ drop 3 (show peek) ++ "`") p
  where
    make0 = do
      v0 <- breakname <$> fetchTerm
      return $ (mkName) v0
    make1 = do
      v0 <- breakliteral <$> fetchTerm
      return $ (return) v0
    make2 = do
      v0 <- breaklpar <$> fetchTerm
      v1 <- parseEXPR
      v2 <- breakrpar <$> fetchTerm
      return $ (\_ e _ -> (\s -> "(" ++ s ++ ")") <$> e) v0 v1 v2

peekTerm :: YGMonad YGTerminal
peekTerm = do
  peek <- get
  case peek of
    TLError a -> throwError a
    TLEof _ -> return YGTEof
    TLCons a _ _ -> return $ snd a

peekPos :: YGMonad Position
peekPos = do
  peek <- get
  case peek of
    TLError a -> throwError a
    TLEof p -> return p
    TLCons _ p _ -> return p

fetchTerm :: YGMonad (Position, YGTok)
fetchTerm = do
  peek <- get
  case peek of
    TLError a -> throwError a
    TLEof p -> return (p, undefined)
    TLCons a p t -> do
      put t
      return (p, fst a)

ensureEof :: YGMonad ()
ensureEof = peekTerm >>= \p -> case p of
    YGTEof -> return ()
    _ -> peekPos >>= \pos -> throwError $ LexError ("expected Eof got " <> show p) pos 

parse :: TokensList YGTok -> Either LexError YGFile
parse = runIdentity . runExceptT . evalStateT (parseFILE <* ensureEof) . ((\x -> (x, mapTok x)) <$>)


module Pysets.Lex (tokenize) where

import Pysets.Tokens
import Pysets.Exc

import Data.Text (Text)
import qualified Data.Text as T
import Data.Char
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State
import Control.Monad
import Control.Monad.Extra

data LState = LState { lpos :: Position, rest :: Text }

instance Pos LState where
	position = lpos

lhas :: State LState Bool
lhas = gets $ not . T.null . rest

lpeek :: State LState Char
lpeek = gets $ T.head . rest

gotoNL :: Position -> Position
gotoNL pos = pos { col = 0, line = line pos + 1 }

lfetch :: State LState Char
lfetch = do
	was <- get
	peek <- lpeek
	let waspos = position was
	let pos = waspos { col = col waspos + 1, absolute = absolute waspos + 1 }
	put was { lpos = if peek == '\n' then gotoNL pos else pos, rest = T.tail $ rest was }
	return peek

fetchNameAccum :: String -> State LState String
fetchNameAccum a = do
	has <- lhas
	if not has then return a else do
		peek <- lpeek
		if isAsciiLower peek
		then lfetch >> fetchNameAccum (peek:a)
		else return a

operators :: Map String (Position -> Token)
operators = Map.fromList [("and", TAnd), ("or", TOr), ("xor", TXor), ("not", TNot), ("in", TIn)]

type TProvider = Position -> Token

wrap :: State LState (Maybe TProvider) -> State LState (Maybe Token)
wrap a = do
	pos <- gets position
	res <- a
	return $ ($ pos) <$> res

fetchName :: State LState (Maybe TProvider)
fetchName = do
	found <- reverse <$> fetchNameAccum ""
	if null found
	then return Nothing
	else
		let isop = Map.lookup found operators in
		return $ Just $ fromMaybe (TName found) isop

simple :: Map Char TProvider
simple = Map.fromList [('(', TLParen), (')', TRParen)]

fetchSimple :: State LState (Maybe TProvider)
fetchSimple = do
	has <- lhas
	if has
	then do
		peek <- lpeek
		let s = Map.lookup peek simple
		when (isJust s) (void lfetch)
		return s
	else return Nothing

skipWS :: State LState ()
skipWS = do
	whenM lhas do
		whenM (isSpace <$> lpeek) (lfetch >> skipWS)

getFewTokens :: State LState (Either ParserError [Token])
getFewTokens = do
	skipWS
	res' <- sequence $ wrap <$> [fetchName, fetchSimple]
	let res = catMaybes res'
	if null res
	then do
		has <- lhas
		pos <- gets position
		if has then return $ Left $ ParserError "can't tokenize" (Just pos)
		else return $ Right []
	else return $ Right res

tokenizeM :: State LState TokenList
tokenizeM = do
	cur <- getFewTokens
	case cur of
		Left err -> return $ ListError err
		Right [] -> return ListEof
		Right l  -> tokenListConverter l <$> tokenizeM
tokenize :: Text -> TokenList
tokenize str =
	evalState tokenizeM LState { rest = str, lpos = Position 0 0 0 }

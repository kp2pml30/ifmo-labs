module YLex.Combinators where

import qualified Data.Text as Text
import Data.Maybe

import Control.Monad.Identity
import Control.Monad.State
import Control.Applicative
import Control.Monad.Trans.Except
import Control.Monad.Except
import Control.Monad.Extra

import YLex.Base

updatePos :: (Int -> Int) -> (Int -> Int) -> (Int -> Int) -> LexMonad us ()
updatePos am lm cm = 
	modify \s ->
		let Position {..} = curPos s in
		s { curPos = Position (lm line) (cm col) (am absolute) }

parseMaybe :: LexMonad us a -> LexMonad us (Maybe a)
parseMaybe a = (Just <$> a) <|> return Nothing

parseEither :: LexMonad us a -> LexMonad us (Either Position a)
parseEither a = (Right <$> a) <|> (Left <$> parsePosition)

runLexMonad (LexMonad m) = runIdentity . runExceptT . runStateT m

ensureNot :: LexMonad us () -> LexMonad us ()
ensureNot f = do
	s0 <- get
	b <- (f >> return True) `catchError` const (return False)
	when b do
		put s0
		parsePosition >>= throwError

parseEof :: LexMonad us ()
parseEof = do
	!t <- gets rest
	unless (Text.null t) (gets curPos >>= throwError)

parseChar :: forall us. LexMonad us Char
parseChar = do
	ensureNot parseEof
	!c <- gets $ Text.head . rest
	modify \s -> s { rest = Text.tail $ rest s }
	if c == '\n'
		then updatePos' (+ 1) (const 0)
		else updatePos' id (+ 1)
	return c
	where
		updatePos' = updatePos (+ 1)

parseCharIf :: (Char -> Bool) -> LexMonad us Char
parseCharIf f = do
	c <- parseChar
	unless (f c) parseError
	return c

chopStr :: Text.Text -> LexMonad us ()
chopStr r = do
	let
		!len = Text.length r
		!nls = Text.length $ Text.filter (== '\n') r
		lastNl = fromMaybe len $ Text.findIndex (== '\n') $ Text.reverse r
	str0 <- gets rest
	updatePos (+ len) (+ nls) (const lastNl)
	modify \s -> s { rest = Text.drop len str0 }

parseStr :: (Char -> Bool) -> LexMonad us Text.Text
parseStr f = do
	str0 <- gets rest
	let r = Text.takeWhile f str0
	let !len = Text.length r
	if not $ f '\n'
	then do
		updatePos (+ len) id (+ len)
		modify \s -> s { rest = Text.drop len str0 }
	else
		chopStr r
	return r

ensureNotEmpty :: LexMonad us Text.Text -> LexMonad us Text.Text
ensureNotEmpty f = do
	r <- f
	when (Text.null r) parseError
	return r

parseStrNE = ensureNotEmpty . parseStr

ensureString :: Text.Text -> LexMonad us ()
ensureString s = do
	let l = Text.length s
	r <- gets rest
	when (s /= Text.take l r) parseError
	chopStr s

noFail :: LexMonad us a -> LexMonad us ()
noFail = (<|> return ()) . void

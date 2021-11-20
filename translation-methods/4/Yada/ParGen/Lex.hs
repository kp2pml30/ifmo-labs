{-# LANGUAGE OverloadedStrings #-}
module Yada.ParGen.Lex (processLexGrammar) where

import qualified Data.Text as Text

import Control.Monad.Writer
import Control.Applicative
import Data.Char
import Data.List

import Yada.ParGen.Combinator

tellnl :: Text.Text -> Writer Text.Text ()
tellnl = tell . (<> "\n")

tell' :: Text.Text -> Writer Text.Text ()
tell' = tell

parseRest = parseWhile (/= '\n')
skipWs = void $ parseWhile isSpace

nop :: Monad m => m ()
nop = return ()

type MMonad = LexMonad () (Writer Text.Text ())

procName :: MMonad
procName = tell <$> liftM2 (<>) (parseWhileNE isAlpha) (parseWhile isAlphaNum)
procChar :: MMonad
procChar =
	(\c -> tell $ "parseCharIf (== " <> Text.pack (show c) <> ")") <$>
		(parseCharIf (== '\'') *> parseChar <* parseCharIf (== '\''))
procStr = (\s -> tell $ "ensureString " <> Text.pack (show s)) <$> (parseCharIf (== '"') *> parseWhile (/= '"') <* parseCharIf (== '"'))

procSmth = procName <|> procChar <|> procStr

parseArrow = ensureString "==>"

proc :: MMonad
proc = do
	userIncludes <- sequence_ <$> many (tellnl <$> (skipWs >> ensureString "-- " >> parseRest))
	stateType <- skipWs >> ensureString "%state " >> parseRest
	tokenType <- skipWs >> ensureString "%token " >> parseRest
	skipWs
	let
		scanner =
			(ensureString "%token" >> return nop)
				<|>
			(liftM2 (>>)
				(tellnl <$> (parseRest <* parseWhile (`elem` ("\r\n" :: String))))
				scanner)
	customFunctions <- scanner
	let
		parseRule = do
			cond <- sequence . intercalate [tell " <*> "] . map singleton <$> some (skipWs >> procSmth)
			act <- tell <$> (skipWs >> parseArrow >> skipWs >> parseRest)
			return (tell "(" >> act >> tell ") <$> " >> cond)
	mainAlternatives <- mapM_ (tell "\n  <|> " >>) <$> many parseRule
	skipWs
	parseEof

	return do
		tellnl "{-# OPTIONS_GHC -w #-}"
		userIncludes
		tell "import Yada.ParGen.Combinator\n\
			\import qualified Data.Text\n\
			\import Control.Applicative\n\
			\\n"
		customFunctions
		tellnl $ "parse :: LexMonad " <> stateType <> " " <> tokenType
		tell "parse = empty"
		mainAlternatives
		tellnl ""

processLexGrammar :: Text.Text -> Either LexError Text.Text
processLexGrammar lg = execWriter . fst <$> runLexMonad proc (defaultLexState () lg)

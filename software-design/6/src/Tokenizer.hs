{-# LANGUAGE
	ScopedTypeVariables
	, TemplateHaskell
	#-}

module Tokenizer where

import Control.Monad.State
import Data.Char (isDigit, isSpace)
import qualified Data.Map as Map
import Control.Lens
import System.IO.Unsafe (unsafePerformIO)
import Text.Read (readMaybe)

import Tokens

data TState
	= TSStart
	| TSNum
	| TSErr
	| TSEnd
	deriving (Show, Eq, Ord, Enum, Bounded)

data TokenizerState a
	= TokenizerState
		{ _rest :: String
		, _tState :: TState
		, _tRes :: [Token a]
		, _tErr :: Maybe String
		, _tAccum :: String
		}
	deriving (Show)

makeLenses ''TokenizerState

emptyTokenizerState rest =
	TokenizerState
		{ _rest = rest
		, _tState = TSStart
		, _tRes = []
		, _tErr = Nothing
		, _tAccum = ""
		}

charToOp =
	Map.fromList
		[ ('+', Add)
		, ('-', Sub)
		, ('*', Mul)
		, ('/', Div)
		]

-- OOP State pattern
parseStream ::
	forall a.
		(Read a)
		=> String
		-> Either String [Token a]
parseStream s =
	let st = execState parser (emptyTokenizerState s) in
	maybe (Right $ reverse $ st ^. tRes) Left (st ^. tErr)
	where
		parser :: State (TokenizerState a) ()
		parser = do
			s <- gets (^. tState)
			case s of
				TSStart ->
					gets (^. rest) >>= \case
						x:xs
							| isDigit x -> do
								modify (tState .~ TSNum)
								parser
							| isSpace x -> do
								modify (rest .~ xs)
								parser
							| x `Map.member` charToOp -> do
								modify (tRes %~ ((TOp $ charToOp Map.! x):))
								modify (rest .~ xs)
								parser
							| x == '(' -> do
								modify (tRes %~ (TLpar:))
								modify (rest .~ xs)
								parser
							| x == ')' -> do
								modify (tRes %~ (TRpar:))
								modify (rest .~ xs)
								parser
						[] -> do
							modify (tState .~ TSEnd)
							parser
						g -> do
							modify (tErr .~ Just ("unexpected tail `" ++ g ++ "`"))
							modify (tState .~ TSErr)
							parser
				TSEnd -> return ()
				TSErr -> return ()
				TSNum ->
					gets (^. rest) >>= \case
						x:xs | isDigit x -> do
							modify (tAccum %~ (x:))
							modify (rest .~ xs)
							parser
						_ -> do
							acc <- gets (^. tAccum)
							let tr = readMaybe $ reverse acc
							case tr of
								Nothing -> do
									modify (tErr .~ Just ("can't parse number from `" ++ acc ++ "`"))
									modify (tState .~ TSErr)
									parser
								Just i -> do
									modify (tRes %~ (TNum i:))
									modify (tAccum .~ "")
									modify (tState .~ TSStart)
									parser

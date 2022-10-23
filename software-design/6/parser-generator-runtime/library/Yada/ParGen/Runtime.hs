{-# LANGUAGE DeriveFunctor #-}
module Yada.ParGen.Runtime where

import qualified Data.Text as Text
import Data.Functor
import Data.List (foldl')

data Position = Position { line :: !Int, col :: !Int, absolute :: !Int } deriving (Eq, Ord)

instance Show Position where
	show Position{..} = show line ++ ":" ++ show col

defaultPosition = Position 0 0 0
noPosition :: Position
noPosition = Position (negate 1) (negate 1) (negate 1)

data LexError
	= LexError
		{ lexErrorMsg :: !String
		, lexErrorPos :: !Position
		}
	deriving (Eq, Ord, Show)

data TokensList a
	= TLEof !Position
	| TLError !LexError
	| TLCons !a !Position (TokensList a)
	deriving (Show, Functor)

tokensListFromList :: [a] -> TokensList a
tokensListFromList a =
	foldl' (\l r -> r l) (TLEof noPosition) $ (\a -> TLCons a noPosition) <$> reverse a

tokensListFromEither :: Either String [a] -> TokensList a
tokensListFromEither =
	\case
		Left err -> TLError $ LexError err noPosition
		Right lst -> tokensListFromList lst

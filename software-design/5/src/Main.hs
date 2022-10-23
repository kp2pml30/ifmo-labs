{-# LANGUAGE ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes,
	FlexibleInstances, UndecidableInstances #-}
module Main where

import Main.Utf8 (withUtf8)
import Control.Monad

import Tokenizer
import Tokens
import Yada.ParGen.Runtime
import Gen.Parser
import Ast
import Visitor

class Divver a where
	divv :: a -> a -> a

instance {-# OVERLAPPABLE #-} Fractional a => Divver a where
	divv = (/)

instance Divver Integer where
	divv = div

instance Divver Int where
	divv = div

eval :: (Num a, Divver a) => [a] -> [PAtom a] -> a
eval s = \case
	[] -> head s
	x:xs ->
		let unpack o = o (head $ tail s) (head s) : (tail $ tail s) in
		case x of
			PANum n -> eval (n:s) xs
			PAOp Add -> eval (unpack (+)) xs
			PAOp Sub -> eval (unpack (-)) xs
			PAOp Mul -> eval (unpack (*)) xs
			PAOp Div -> eval (unpack divv) xs

runRoutines :: forall a. (Read a, Show a, Num a, Divver a) => String -> IO ()
runRoutines s = do
	putStrLn s
	let tokens = parseStream s :: Either String [Token a]
	print tokens
	let tokLst = tokensListFromEither tokens
	print tokLst
	let parsed = parse tokLst
	print parsed
	print (flip visit PrintVis <$> parsed :: Either LexError String)
	let pol = reverse . flip visit ToPolVis <$> parsed :: Either LexError [PAtom a]
	print pol
	print $ eval [] <$> pol
	putStrLn ""

main = withUtf8 do
	runRoutines @Int "(1 + 2) * 3"
	runRoutines @Int "(1 + 2) / 2"
	runRoutines @Int "1 + 1 / 2"
	runRoutines @Float "1 + 1 / 2"
	forever do
		s <- getLine
		runRoutines @Float s

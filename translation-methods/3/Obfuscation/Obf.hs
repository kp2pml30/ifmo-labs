module Obfuscation.Obf where

import Control.Monad
import Control.Monad.Reader
import Data.Foldable
import qualified Data.Map as Map

type Inserter = MyState -> String -> String

data MyState = MyState { seed :: Int, names :: Map.Map String String, inserter :: Inserter }

type Md = Reader MyState String

processArgs = undefined

sepCat :: Char -> [String] -> String
sepCat _ [] = ""
sepCat c l = tail $ foldl' (\x y -> x ++ [c] ++ y) "" l

bodyDecl :: (String, String, Md) -> Md -> Md
bodyDecl (t, n, v) b = do
	vres <- v
	was <- ask
	let newName = inserter was was n
	let upd = was { names = Map.insert n newName (names was) }
	bres <- local (const upd) b
	return $ t ++ " " ++ newName ++ "=" ++ vres ++ ";" ++ bres
	-- foldl' (++) "" <$> sequence b -- todo : rework sequence

bopLift :: String -> Md -> Md -> Md
bopLift o l r = do
	ml <- l
	mr <- r
	return $ ml ++ o ++ mr

seqCat :: Char -> [Md] -> Md
seqCat sep l = do
	r <- sequence l
	return $ sepCat sep r

mkCall :: Md -> Md -> Md
mkCall e a = do
	call <- e
	args <- a
	return $ call ++ "(" ++ args ++ ")"

mkIf :: Md -> Md -> Md -> Md
mkIf c t e =
	liftM3 (\a b c -> a ++ b ++ c)
		((\x -> "if(" ++ x ++ "){") <$> c)
		((++ "}") <$> t)
		e

mkFunc :: String -> [(String, String)] -> Md -> Md
mkFunc n a b = do
	was <- ask
	let upd = foldl' (\a@MyState { names, inserter } (_,x) -> a { names = Map.insert x (inserter a x) names }) was a
	bs <- local (const upd) b
	let nameMapper = (names upd Map.!)
	return $ n ++ "(" ++ sepCat ',' (map (\(x,y) -> x ++ " " ++ nameMapper y) a) ++ "){" ++ bs ++ "}"

mkName :: String -> Md
mkName n = do
	r <- reader names
	return $ Map.findWithDefault n n r

insId _ = id
insRev _ = reverse

insI1O0 ms _ =
	let size = Map.size (names ms) in
	genStr size

genStr i =
	(if even i then 'I' else 'O') : helper (i `div` 2)
	where
		helper 0 = ""
		helper i = (case i `mod` 4 of
			0 -> '0'
			1 -> 'I'
			2 -> '1'
			3 -> 'O'
			_ -> undefined) : helper (i `div` 4)

evalParse :: Inserter -> [Md] -> String
evalParse ins = foldMap (`runReader` (MyState 0 Map.empty ins))

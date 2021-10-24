module Obfuscation.Obf where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Data.Foldable
import qualified Data.Map as Map

type Inserter = String -> Md

data MyState = MyState { names :: Map.Map String String, inserter :: Inserter, randomizer :: Md }

type MdR r = ReaderT MyState (State [Int]) r
type Md = MdR String

runMd s m = flip evalState s . flip runReaderT m

fetchSeed :: MdR Int
fetchSeed = do
	modify tail
	gets head

sepCat :: Char -> [String] -> String
sepCat _ [] = ""
sepCat c l = tail $ foldl' (\x y -> x ++ [c] ++ y) "" l

evalInsert :: String -> MdR (MyState, String)
evalInsert n = do
	was <- ask
	insN <- inserter was n
	let newState = was { names = Map.insertWith (const id) n insN (names was) }
	return (newState, names newState Map.! n)

rndAction :: Md -> Md
rndAction x = do
	r <- (\x -> x `mod` 4 + 1) <$> fetchSeed
	rnd <- reader randomizer
	res <- replicateM r rnd
	xres <- x
	return $ mconcat res ++ xres

bodyDecl :: (String, String, Md) -> Md -> Md
bodyDecl (t, n, v) b = do
	vres <- v
	(upd, newName) <- evalInsert n
	bres <- local (const upd) b
	return $ t ++ " " ++ newName ++ "=" ++ vres ++ ";" ++ bres

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
mkIf c t =
	liftM3 (\a b c -> a ++ b ++ c)
		((\x -> "if(" ++ x ++ "){") <$> c)
		((++ "}") <$> t)
		-- eta reduced else

mkFunc :: String -> [(String, String)] -> Md -> Md
mkFunc n a b = do
	res <- mkArgs a
	return $ n ++ "(" ++ res
	where
		mkArgs [] = (\x -> "){" ++ x ++ "}") <$> b
		mkArgs [(t, n)] = do
			(ns, nn) <- evalInsert n
			body <- local (const ns) b
			return $ t ++ " " ++ nn ++ "){" ++ body ++ "}"
		mkArgs ((t, n):xs) = do
			(ns, nn) <- evalInsert n
			rest <- local (const ns) (mkArgs xs)
			return $ t ++ " " ++ nn ++ "," ++ rest

mkName :: String -> Md
mkName n = do
	r <- reader names
	return $ Map.findWithDefault n n r

insId :: Inserter
insId = return
insRev :: Inserter
insRev = return . reverse

insI1O0 :: Inserter
insI1O0 _ = do
	size <- reader $ Map.size . names
	seed <- fetchSeed
	return $ genStr (size + seed)
	where
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

evalParseHelp rnd seeds ins =
	foldMap (runMd (cycle seeds) $ MyState Map.empty ins rnd)

-- todo
insertSmth :: Md
insertSmth = return ";"

evalParseRnd :: [Int] -> Inserter -> [Md] -> String
evalParseRnd = evalParseHelp do
		s <- fetchSeed
		if even s
		then return ""
		else do
			return ";"

evalParse :: Inserter -> [Md] -> String
evalParse = evalParseHelp (return "") [0]

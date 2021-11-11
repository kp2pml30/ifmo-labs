module Obfuscation.Obf where

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Data.Foldable
import Data.Char (chr)
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

mkWhile :: Md -> Md -> Md
mkWhile c t =
	liftM2 (++)
		((\x -> "while(" ++ x ++ "){") <$> c)
		((++ "}") <$> t)


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

genI1O0Str i = 'I' : helperO i -- if even i then 'I' : helperO (i `div` 2) else 'O' : helperI (i `div` 2)
			where
				helperI 0 = ""
				helperI i = (if even i then 'I' else '1') : helperO (i `div` 2)
				helperO 0 = ""
				helperO i = (if even i then 'O' else '0') : helperI (i `div` 2)

insI1O0Bound :: Int
insI1O0Bound = 2 ^ (30 :: Int)
insI1O0Offset :: Int
insI1O0Offset = 0xffff

insI1O0 :: Inserter
insI1O0 _ = do
	size <- reader $ Map.size . names
	seed <- (\x -> x `mod` (insI1O0Bound  - insI1O0Offset) + insI1O0Bound) <$> fetchSeed
	return $ genI1O0Str (size + seed)

insI1O02 = do
	seed <- (\x -> insI1O0Bound * 2 - x `mod` insI1O0Offset) <$> fetchSeed
	return $ genI1O0Str seed


evalParseHelp rnd seeds ins =
	foldMap (runMd (cycle seeds) $ MyState Map.empty ins rnd)

selectOneOf :: [a] -> MdR a
selectOneOf lst = do
	let len = length lst
	r <- (`mod` len) <$> fetchSeed
	return $ lst !! r

makeStringLiteral :: Md
makeStringLiteral = do
	r <- (`mod` 16) <$> fetchSeed
	gen r ['"']
	where
		gen 0 s = return $ '"' : s
		gen x s = do
			c <- (\s -> s `mod` (91 - 38) + 38) <$> fetchSeed
			gen (x - 1) ((chr c):s)

makeIntLiteral :: Md
makeIntLiteral = do
	(\x -> show $ x `mod` 65536) <$> fetchSeed

makeVarRead :: Md
makeVarRead = do
	mp <- reader names
	let sz = Map.size mp
	if sz == 0
	then makeIntLiteral
	else do
		r <- (`mod` Map.size mp) <$> fetchSeed
		-- return $ snd $ Map.elemAt r mp -- problem on x64
		return $ "(int)" ++ snd (Map.elemAt r mp)

insertAtom :: Md
insertAtom = do
	join $ selectOneOf
		[ makeIntLiteral
		, (\s -> "strlen(" ++ s ++ ")") <$> makeStringLiteral
		, (\s -> "atoi(" ++ s ++ ")") <$> makeStringLiteral
		, (\s1 s2 -> "strcmp(" ++ s1 ++ "," ++ s2 ++ ")") <$> makeStringLiteral <*> makeStringLiteral
		-- , return "rand()"
		, makeVarRead
		]

insertExpr :: Md
insertExpr  =
	helper (5 :: Int)
	where
		helper 0 = insertAtom
		helper n =
			let h = helper (n - 1) in
				join $ selectOneOf
					[ insertAtom
					, (\s -> "(" ++ s ++ ")") <$> h
					, (\a b -> a ++ "+" ++ b) <$> h <*> h
					, (\a b -> a ++ "*" ++ b) <$> h <*> h
					, (\a b -> a ++ "-" ++ b) <$> h <*> h
					]

insertSmth :: Md
insertSmth = join $ selectOneOf
	[ (++ ";") <$> insertExpr
	, liftM2
			(\x v -> "int " ++ {- map (\c -> if c == 'O' then 'Q' else c) -} x ++ " = " ++ v ++ ";")
			insI1O02
			insertExpr
	]

evalParseRnd :: [Int] -> Inserter -> [Md] -> String
evalParseRnd = evalParseHelp do
		s <- fetchSeed
		if even s
		then return ""
		else insertSmth

evalParse :: Inserter -> [Md] -> String
evalParse = evalParseHelp (return "") [0]

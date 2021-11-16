{-# LANGUAGE OverloadedStrings #-}

module YPar.Par (Grammar(..), parseGrammar, processGrammar) where

import qualified Data.Text as Text
import qualified Data.Map  as Map
import qualified Data.Set  as Set
import Data.Char
import Data.List (group, sort)
import Data.Foldable
import Control.Applicative
import Control.Monad
import Control.Monad.Writer (Writer, execWriter, tell)

import YLex.Base
import YLex.Combinators

tshow :: Show s => s -> Text.Text
tshow = Text.pack . show

data Terminal
	= Terminal
		{ tCond   :: Text.Text
		, tAction :: Text.Text
		}
	deriving (Eq, Show)

data NTAtom
	= ATerm  Text.Text
	| ANTerm Text.Text
	deriving (Eq, Show)

data NTerminal
	= NTerminal
		{ ntCond   :: [NTAtom]
		, ntAction :: Text.Text
		}
	deriving (Eq, Show)

data Grammar
	= Grammar
		{ imports    :: [Text.Text]
		, tokenType  :: Text.Text
		, fileType   :: Text.Text
		, terminals  :: [(Text.Text, [Terminal])]
		, nterminals :: [(Text.Text, [NTerminal])]
		}
	deriving (Eq, Show)

skipWs = parseStr isSpace >> noFail (parseCharIf (== '#') >> parseStr (/= '\n') >> skipWs)

parseRest = parseStr (/= '\n')

parseTerminal = parseStrNE isAsciiLower
parseNTerminal = parseStrNE isAsciiUpper

parseNTorT = ANTerm <$> parseNTerminal <|> ATerm <$> parseTerminal

parseCase = do
	skipWs
	liftM2 (,)
		parseTerminal
		(some parseAlt)
	where
		parseAlt = do
			skipWs
			ensureString "<=="
			skipWs
			cnd <- parseRest
			Terminal cnd <$> ((skipWs >> ensureString "==>" >> skipWs >> parseRest) <|> return "()")

data Associativity = AssocLeft | AssocRight deriving (Eq, Enum, Show, Ord)

parseOperator :: LexMonad () [(Text.Text, [NTerminal])]
parseOperator = do
	skipWs
	ensureString "%oper"
	skipWs
	assoc <- (ensureString "l" >> return AssocLeft) <|> (ensureString "r" >> return AssocRight) <|> parseErrorStr "unknown associativity"
	skipWs
	name <- parseNTerminal
	skipWs
	op <- parseNTorT
	skipWs
	smaller <- parseNTorT
	skipWs
	action1 <- (ensureString "==>" >> skipWs >> parseRest) <|> return "id"
	skipWs
	let name' = name <> "'"
	return case assoc of
			AssocLeft ->
				[ (name, [NTerminal [smaller, ANTerm name'] "\\l o -> o l"])
				, (name', [NTerminal [] action1, NTerminal [op, smaller, ANTerm name'] "\\o r u l -> u (o l r)"])
				]
			AssocRight ->
				[ (name, [NTerminal [smaller, ANTerm name'] "\\l o -> o l"])
				, (name', [NTerminal [] action1, NTerminal [op, smaller, ANTerm name'] "\\o r u l -> o l (u r)"])
				]

parseRule :: LexMonad () (Text.Text, [NTerminal])
parseRule = do
	skipWs
	liftM2 (,)
		parseNTerminal
		(some parseAlt)
	where
		parseAlt = do
			skipWs
			ensureString "|"
			liftM2 NTerminal
				(many (skipWs >> parseNTorT))
				(skipWs >> ensureString "==>" >> skipWs >> parseRest)

parseGrammar :: Text.Text -> Either LexError Grammar
parseGrammar t = fst <$> runLexMonad
		(do
			r <- Grammar
				<$> (many parseImport)
				<*> (skipWs >> ensureString "%token " >> parseRest)
				<*> (skipWs >> ensureString "%file " >> parseRest)
				<*> (some parseCase)
				<*> (concat <$> some (parseOperator <|> (:[]) <$> parseRule))
			skipWs
			parseEof
			return r)
		(defaultLexState () t)
	where
		parseImport = skipWs >> ensureString "-- " >> parseRest

terminalName s = "YGT" <> Text.pack [toUpper $ Text.head s] <> Text.drop 1 s

makeTerminals :: [(Text.Text, [Terminal])] -> Writer Text.Text ()
makeTerminals t = do
	let l = map head $ group $ sort $ map (terminalName . fst) t
	tell "data YGTerminal"
	tell $ "\n  = " <> head l
	mapM_ (\x -> tell $ "\n  | " <> x) (tail l)
	tell $ "\n  | " <> terminalName "eof"
	tell "\n  deriving (Eq, Ord, Show, Enum)\n"

type First = Map.Map Text.Text (Map.Map Text.Text Int)

type Follow = Map.Map Text.Text (Set.Set Text.Text)

checkedMerge err k a b =
	if a /= b
	then error $ "can't merge " ++ show a ++ " and " ++ show b ++ " for " ++ show k ++ "\n" ++ err
	else a

whileChanges :: Eq a => (a -> a) -> a -> a
whileChanges f old =
	let new = f old in
	if old /= new
	then whileChanges f new
	else old

buildFirst :: [(Text.Text, Int, [NTAtom])] -> First
buildFirst l =
	let (newRules, strt) = initializeWithTerminals in
	let
		update st =
			let
				folder :: First -> (Text.Text, Int, [NTAtom]) -> First
				folder accum (_, _, []) = accum
				folder accum (k, i, ATerm a : _) =
					Map.adjust
						(Map.insertWithKey
							(checkedMerge $ "populating " ++ Text.unpack k)
							a
							i)
						k
						accum
				folder accum (k, i, ANTerm a : tail) =
					let aset = i <$ accum Map.! a in
					let nxt = Map.adjust
						(Map.unionWithKey (checkedMerge $ "populating " ++ Text.unpack k) aset)
						k
						accum in
					if "" `Map.member` aset
					then folder nxt (k, i, tail)
					else nxt
			in foldl' folder st newRules
	in whileChanges update strt
	where
		initializeWithTerminals :: ([(Text.Text, Int, [NTAtom])], First)
		initializeWithTerminals =
			let
				start :: First
				start = Map.fromList [(x, Map.empty) | (x, _, _) <- l]
				folder ::
					([(Text.Text, Int, [NTAtom])], First) ->
						(Text.Text, Int, [NTAtom]) ->
						([(Text.Text, Int, [NTAtom])], First)
				folder (al, am) (nt, i, rule) =
					case rule of
						[] -> (al, Map.adjust (Map.insert "" i) nt am)
						ATerm term : _ ->
							( al
							, Map.adjust
								(Map.insertWithKey
									(checkedMerge $ "during initialization of " ++ Text.unpack nt)
									term
									i)
								nt
								am)
						_ -> ((nt, i, rule):al, am)
			in foldl' folder ([], start) l

applyWhen :: Bool -> (a -> a) -> a -> a
applyWhen False _ a = a
applyWhen True f a = f a

buildFollow :: First -> [(Text.Text, Int, [NTAtom])] -> Follow
buildFollow first' l =
	let
		first = Map.keysSet <$> first'
		initial :: Follow
		initial = Map.adjust (Set.insert "") "FILE" $ Set.empty <$ first
		updateOne follow (a, _, atoms) =
			let
				updateOneOne :: NTAtom -> (Follow, Set.Set Text.Text) -> (Follow, Set.Set Text.Text)
				updateOneOne (ATerm b) (follow, _) = (follow, Set.singleton b)
				updateOneOne (ANTerm b) (follow, gammafst) =
					let bfirst = first Map.! b in
					let changed = Map.adjust (Set.union $ Set.delete "" gammafst) b follow in
					( applyWhen ("" `Set.member` gammafst) (Map.adjust (Set.union $ changed Map.! a) b) changed
					, if "" `Set.member` (first Map.! b) then gammafst `Set.union` bfirst else bfirst
					) in
			fst $ foldr updateOneOne (follow, Set.singleton "") atoms
		update follow = foldl' updateOne follow l
	in
	whileChanges update initial

tellnl :: Text.Text -> Writer Text.Text ()
tellnl = tell . (<> "\n")

showFirst :: First -> Text.Text
showFirst first =
	execWriter do
		mapM_ (\(k, v) -> tellnl k >> mapM_ (\(k, v) -> tellnl ("\t" <> k <> "\t" <> tshow v)) (Map.toList v)) $ Map.toList first

showFollow :: Follow -> Text.Text
showFollow first =
	execWriter do
		mapM_ (\(k, v) -> tellnl k >> mapM_ (tellnl . ("\t" <>)) v) $ Map.toList first

processGrammar :: Grammar -> Text.Text
processGrammar Grammar {..} =
	let
		!catNTerminals = nterminals >>= \(a, l) -> [(a, i, ntCond x) | (i, x) <- zip [0..] l]
		!first = buildFirst catNTerminals
		!follow = buildFollow first catNTerminals in
	execWriter do
			tellnl "{-# OPTIONS_GHC -w #-}"
			mapM_ tellnl imports

			tellnl "{-"
			tellnl " -- first --"
			tellnl $ showFirst first
			tellnl " -- follow --"
			tellnl $ showFollow follow
			tellnl "-}"

			tellnl "import Control.Monad.Identity"
			tellnl "import Control.Monad.Except"
			tellnl "import Control.Monad.Trans.Except"
			tellnl "import Control.Monad.State"
			tellnl "import YLex.Lex (TokensList(..))"
			tellnl "import YLex.Base (LexError(..), Position)"
			tellnl ""

			makeTerminals terminals
			tellnl ""

			tellnl $ "type YGTok = " <> tokenType
			tellnl $ "type YGFile = " <> fileType
			tellnl $ "type YGMonad = StateT (TokensList (YGTok, YGTerminal)) (ExceptT LexError Identity)"
			tellnl ""

			tellnl "mapTok :: YGTok -> YGTerminal"
			tellnl "mapTok tok = case tok of"
			mapM_ (\(name, cases) -> mapM_ (mapTerm name) cases) terminals
			tellnl ""

			mapM_ (uncurry makeBreaker) (terminals >>= \(n, ca) -> zip (repeat n) ca)
			tellnl ""
			mapM_ (uncurry $ makeParser first follow) nterminals
			tellnl ""

			tell "peekTerm :: YGMonad YGTerminal\n\
				\peekTerm = do\n\
				\  peek <- get\n\
				\  case peek of\n\
				\    TLError a -> throwError a\n\
				\    TLEof _ -> return YGTEof\n\
				\    TLCons a _ _ -> return $ snd a\n\
				\\n"

			tell "peekPos :: YGMonad Position\n\
				\peekPos = do\n\
				\  peek <- get\n\
				\  case peek of\n\
				\    TLError a -> throwError a\n\
				\    TLEof p -> return p\n\
				\    TLCons _ p _ -> return p\n\
				\\n"

			tell "fetchTerm :: YGMonad (Position, YGTok)\n\
				\fetchTerm = do\n\
				\  peek <- get\n\
				\  case peek of\n\
				\    TLError a -> throwError a\n\
				\    TLEof p -> return (p, undefined)\n\
				\    TLCons a p t -> do\n\
				\      put t\n\
				\      return (p, fst a)\n\
				\\n"

			tell "ensureEof :: YGMonad ()\n\
				\ensureEof = peekTerm >>= \\p -> case p of\n\
				\    YGTEof -> return ()\n\
				\    _ -> peekPos >>= \\pos -> throwError $ LexError (\"expected Eof got \" <> show p) pos \n\
				\\n"

			tellnl "parse :: TokensList YGTok -> Either LexError YGFile"
			tellnl "parse = runIdentity . runExceptT . evalStateT (parseFILE <* ensureEof) . ((\\x -> (x, mapTok x)) <$>)"
	where
		mapTerm name Terminal { tCond } = tellnl $ "  " <> tCond <> " -> " <> terminalName name
		makeParser :: First -> Follow -> Text.Text -> [NTerminal] -> Writer Text.Text ()
		makeParser first follow name alternatives = do
			when (name == "FILE") $ tellnl "parseFILE :: YGMonad YGFile"
			tellnl $ "parse" <> name <> " = do\n  peek <- peekTerm\n  case peek of"
			mapM_ makeCase $ Map.toList $ first Map.! name
			let
				makeFollowed f = do
					let
						!myFollow' = follow Map.! name
						!myFollow = Set.delete "" myFollow'
					mapM_ (f . terminalName) myFollow
					when ("" `Set.member` myFollow') (f "YGTEof")
			mapM_
				(\i -> makeFollowed (\s -> tellnl $ "    " <> s <> " -> make" <> tshow i))
				(Map.lookup "" $ first Map.! name)
			tellnl $ "    _ -> peekPos >>= \\p -> throwError $ LexError (\"can't parse `" <> name <> "` from `\" ++ drop 3 (show peek) ++ \"`\") p"
			tellnl $ "  where"
			mapM_ (uncurry makeAlt) $ zip [0 :: Int ..] alternatives
			where
				makeCase (k, v) =
					when (k /= "") $ tellnl $ "    " <> terminalName k <> " -> make" <> tshow v
				makeAlt i NTerminal {..} = do
					tellnl $ "    make" <> tshow i <> " = do"
					zipWithM_
						(\i x -> tell ("      v" <> tshow i <> " <- ") >> mkAct x)
						[0 :: Int ..]
						ntCond
					tell $ "      return $ (" <> ntAction <> ")"
					let !n = length ntCond
					mapM_ (\x -> tell $ " v" <> tshow x) [0..n - 1]
					tellnl ""
				mkAct :: NTAtom -> Writer Text.Text ()
				mkAct (ATerm a) = tellnl $ "break" <> a <> " <$> fetchTerm"
				mkAct (ANTerm a) = tellnl $ "parse" <> a
		makeBreaker :: Text.Text -> Terminal -> Writer Text.Text ()
		makeBreaker name Terminal {..} = do
			tellnl $ "break" <> name <> " (pos, tok@(" <> tCond <> ")) = " <> tAction


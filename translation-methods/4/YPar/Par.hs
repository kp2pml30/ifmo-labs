{-# LANGUAGE OverloadedStrings #-}

module YPar.Par (Grammar(..), parseGrammar, processGrammar) where

import qualified Data.Text as Text
import qualified Data.Map  as Map
import qualified Data.Set  as Set
import Data.Char
import Data.Foldable
import Control.Applicative
import Control.Monad
import Control.Monad.Writer (Writer, execWriter, tell)

import YLex.Base
import YLex.Combinators

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
		, fileType  :: Text.Text
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
			Terminal cnd <$> ((skipWs >> ensureString "==>" >> skipWs >> parseRest) <|> return "const2 ()")

data Associativity = AssocLeft | AssocRight deriving (Eq, Enum, Show, Ord)

parseOperator :: LexMonad () [(Text.Text, [NTerminal])]
parseOperator = do
	skipWs
	ensureString "%oper"
	skipWs
	assoc <- (ensureString "l" >> return AssocLeft) <|> parseErrorStr "unknown associativity"
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
	return
		[ (name, [NTerminal [smaller, ANTerm name'] "flip ($)"])
		, (name', [NTerminal [] action1, NTerminal [op, smaller, ANTerm name'] "const $ flip ($)"])
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
			r <- liftM5 Grammar
				(many parseImport)
				(skipWs >> ensureString "%token " >> parseRest)
				(skipWs >> ensureString "%file " >> parseRest)
				(some parseCase)
				(concat <$> some (parseOperator <|> (:[]) <$> parseRule))
			skipWs
			parseEof
			return r)
		(defaultLexState () t)
	where
		parseImport = skipWs >> ensureString "-- " >> parseRest

terminalName s = "YGT" <> Text.pack [toUpper $ Text.head s] <> Text.drop 1 s

makeTerminals :: [(Text.Text, [Terminal])] -> Writer Text.Text ()
makeTerminals t = do
	let l = map (terminalName . fst) t
	tell "data YGTerminals"
	tell $ "\n  = " <> head l
	mapM_ (\x -> tell $ "\n  | " <> x) (tail l)
	tell $ "\n  | " <> terminalName "eof"
	tell "\n  deriving (Eq, Ord, Show, Enum)\n"

type First = Map.Map Text.Text (Set.Set Text.Text)

buildFirst :: [(Text.Text, [NTAtom])] -> First
buildFirst l =
	let (newRules, strt) = initializeWithTerminals in
	let
		update st =
			let
				folder :: First -> (Text.Text, [NTAtom]) -> First
				folder accum (_, []) = accum
				folder accum (k, ATerm a : _) = Map.adjust (Set.insert a) k accum
				folder accum (k, ANTerm a : tail) =
					let aset = accum Map.! a in
					let nxt = Map.adjust (Set.union aset) k accum in
					if "" `Set.member` aset
					then folder nxt (k, tail)
					else nxt
			in foldl' folder st newRules
		spin old =
			let new = update old in
			if new /= old
			then spin new
			else old
	in spin strt
	where
		initializeWithTerminals =
			let
				start :: First
				start = Map.fromList [(fst x, Set.empty) | x <- l]
				folder ::
					([(Text.Text, [NTAtom])], First) ->
						(Text.Text, [NTAtom]) ->
						([(Text.Text, [NTAtom])], First)
				folder (al, am) (nt, rule) =
					case rule of
						[] -> (al, Map.adjust (Set.insert "") nt am)
						ATerm term : _ -> (al, Map.adjust (Set.insert term) nt am)
						_ -> ((nt, rule):al, am)
			in foldl' folder ([], start) l

tellnl :: Text.Text -> Writer Text.Text ()
tellnl = tell . (<> "\n")

{-
showFirst :: First -> Text.Text
showFirst first =
	execWriter do
		mapM_ (\(k, v) -> tellnl k >> mapM_ (\s -> tellnl ("\t" <> s)) (Set.toList v)) $ Map.toList first
-}

makeParsers :: First -> First -> [(Text.Text, [NTerminal])] -> Writer Text.Text ()
makeParsers first follow =
	mapM_ $ uncurry makeParser
	where
		makeParser :: Text.Text -> [NTerminal] -> Writer Text.Text ()
		makeParser name alternatives = tellnl ("parse" <> name <> " = undefined")
processGrammar :: Grammar -> Text.Text
processGrammar Grammar {..} =
	let first = buildFirst $ nterminals >>= (\(a, l) -> [(a, ntCond x) | x <- l]) in
	execWriter do
			mapM_ tellnl imports

			tellnl "import Control.Monad.Identity"
			tellnl "import Control.Monad.Except"
			tellnl "import Control.Monad.Trans.Except"
			tellnl "import Control.Monad.State"
			tellnl "import YLex.Lex (TokensList(..))"
			tellnl "import YLex.Base (LexError(..))"

			tellnl "const2 = const . const"
			makeTerminals terminals

			tellnl $ "type YGTok = " <> tokenType
			tellnl $ "type YGFile = " <> fileType
			tellnl $ "type YGMonad = StateT (Maybe YGTerminals, TokensList YGTok) (ExceptT LexError Identity)"

			tell "\
				\ygPeek :: YGMonad YGTerminals\n\
				\ygPeek = do\n\
				\  cached <- gets fst\n\
				\  case cached of\n\
				\    Just a -> return a\n\
				\    Nothing -> do\n\
				\      ns <- reeval\n\
				\      modify \\(_, s) -> (Just ns, s)\n\
				\      return ns\n\
				\  where\n\
				\    reeval = do\n\
				\      p <- gets snd\n\
				\      case p of\n\
				\        TLError e -> lift $ throwError e\n\
				\        TLEof -> return YGTEof\n"

			mapM_ (\(name, cases) -> mapM_ (mapTerm name) cases) terminals

			makeParsers first undefined nterminals

			tellnl "\nparse :: TokensList YGTok -> Either LexError YGFile\nparse = runIdentity . runExceptT . fst . runStateT parseFILE\n"
	where
		mapTerm name Terminal { tCond } = tellnl $ "        TLCons (" <> tCond <> ") _ _ -> return " <> terminalName name

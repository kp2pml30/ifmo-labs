module HW3.Parser (HW3.Parser.parse) where

import Control.Applicative hiding (many, some)
import Control.Monad.Combinators.Expr
import Data.ByteString (ByteString)
import qualified Data.ByteString as ByteString
import Data.Char
import Data.Foldable (foldl')
import Data.Functor
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Text as Text
import Data.Void
import Data.Word
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer (charLiteral, hexadecimal, scientific, signed)

import HW3.Base
import HW3.FunctionStrings

-- parser invariant: spaces in the end are skipped
type Pars = Parsec Void String

ratParser :: Pars Rational
ratParser = toRational <$> signed space scientific

-- | list of all named constants
constants :: Map String HiValue
constants = Map.fromList $
  [ ("true", HiValueBool True)
  , ("false", HiValueBool False)
  , ("null", HiValueNull)
  , ("cwd", HiValueAction HiActionCwd)
  , ("now", HiValueAction HiActionNow)
  ]
  ++ (fmap HiValueFunction <$> allFunctions) -- map all second elements

-- | constants parsing function (null/false/..)
constParser :: Pars HiValue
constParser = parseId >>= maybe (empty <?> "unknown constant") pure . (`Map.lookup` constants)

-- | short version to make function application to a given fnction
makeFunAppl :: HiFun -> [HiExpr] -> HiExpr
makeFunAppl = HiExprApply . HiExprValue . HiValueFunction

-- | parse exactly one postfix operator (function application or a bang)
-- for some reason more than 1 is disallowed
parseOnePostfixOperator :: Pars (HiExpr -> HiExpr)
parseOnePostfixOperator =
  (parenList '(' ')' <&> flip HiExprApply)
    <|>
  (char '!' *> space $> makeFunAppl HiExprRun . listSingleton)
    <|>
  (char '.' *> space *> parseId <&> flip HiExprApply . listSingleton . HiExprValue . HiValueString . Text.pack)

parseId :: Pars String
parseId = List.intercalate "-" <$> ((:) <$> satisfy isAlpha <*> many (satisfy isAlphaNum)) `sepBy1` char '-'

operatorsTable :: [[Operator Pars HiExpr]]
operatorsTable =
  [ [ Postfix $
        foldl'
          (flip (.)) -- we want to apply leftmost function first
          id
        <$> some parseOnePostfixOperator
    ]
  , [ InfixL $ notFollowedBy (string "/=") >> char '/' >> space $> makeBopApply HiFunDiv -- binaryl "/" HiFunDiv
    , binaryl "*" HiFunMul
    ]
  , [ binaryl "+" HiFunAdd
    , binaryl "-" HiFunSub
    ]
  , [ binaryn "<" HiFunLessThan
    , binaryn ">" HiFunGreaterThan
    , binaryn ">=" HiFunNotLessThan
    , binaryn "<=" HiFunNotGreaterThan
    , binaryn "==" HiFunEquals
    , binaryn "/=" HiFunNotEquals
    ]
  , [ binaryr "&&" HiFunAnd
    ]
  , [ binaryr "||" HiFunOr
    ]
  ]
  where
    binary :: (Pars BopType -> Operator Pars HiExpr) -> String -> HiFun -> Operator Pars HiExpr
    binary ctor name f = ctor (string name <* space $> makeBopApply f)
    binaryl = binary InfixL
    binaryn = binary InfixN
    binaryr = binary InfixR

type BopType = HiExpr -> HiExpr -> HiExpr

-- | create application fror function of 2 arguments (list-uncurry)
makeBopApply :: HiFun -> BopType
makeBopApply o l r = HiExprApply (HiExprValue $ HiValueFunction o) [l, r]

stringLiteral :: Pars String
stringLiteral = char '"' >> manyTill charLiteral (char '"')

-- | parse list, allows expressions in values
arrayLiteral :: Pars HiExpr
arrayLiteral = makeFunAppl HiFunList <$> (space *> parenList '[' ']')

bytesLiteral :: Pars ByteString
bytesLiteral = ByteString.pack <$> do
  _ <- string "[#"
  space
  manyTill
    (do
      pos0 <- getOffset
      hd :: Word8 <- hexadecimal
      pos1 <- getOffset
      space
      if pos1 - pos0 /= 2
      then empty <?> "byte in [00; ff]"
      else return hd)
    (string "#]" *> space)

-- | parse list, allows expressions in both keys and values
dictLiteral :: Pars HiExpr
dictLiteral = HiExprDict <$>
  inParen
    "{"
    "}"
    (char ',' *> space)
    (liftA2 (,) parser (char ':' *> space *> parser))

valueParser :: Pars HiValue
valueParser =
    HiValueNumber <$> ratParser
    <|> constParser
    -- <|> HiValueFunction <$> funParser
    <|> HiValueString . Text.pack <$> stringLiteral
    <|> HiValueBytes <$> bytesLiteral

inParen :: String -> String -> Pars () -> Pars a -> Pars [a]
inParen lpar rpar sep parser =
  string lpar *> space *>
    (parser `sepBy` sep)
  <* string rpar <* space

parenList :: Char -> Char -> Pars [HiExpr]
parenList b a =
  inParen
    [b]
    [a]
    (char ',' *> space)
    parser

atom :: Pars HiExpr
atom =
  (   char '(' *> parser <* char ')'
  <|> HiExprValue <$> valueParser
  <|> arrayLiteral
  <|> dictLiteral
  ) <* space

expr :: Pars HiExpr
expr = makeExprParser atom operatorsTable <?> "expression"

parser :: Pars HiExpr
parser = space *> expr <* space

parse :: String -> Either (ParseErrorBundle String Void) HiExpr
parse = runParser (space *> parser <* space <* eof) ""

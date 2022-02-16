{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections              #-}

module HW2.T6 where

import Control.Applicative
import Control.Monad
import Data.Char
import Data.Maybe (fromMaybe)
import Data.Foldable
import Numeric.Natural

import Data.Scientific (toRealFloat)

import HW2.T1 hiding (Pair (..))
import HW2.T4
import HW2.T5

newtype ParseError = ErrorAtPos Natural

newtype Parser a = P (ExceptState ParseError (Natural, String) a)
  deriving newtype (Functor, Applicative, Monad)

instance MonadPlus Parser

-- | execute Parser from the beginning (position 0)
runP :: Parser a -> String -> Except ParseError a
runP (P a) s =
  let result = runES a (0, s) in
  case result of
    Error e                -> Error e
    -- Success (a :# _) -> Success a
    Success (a :# (_, [])) -> Success a
    Success (_ :# (p,  _)) -> Error $ ErrorAtPos p

-- | get head of rest of string, fail on EOF
pChar :: Parser Char
pChar =
  -- construct our Parser that wraps ExceptState
  P $ ES \(pos, s) ->
  -- old state s
  case s of
    -- empty => error no char
    []     -> Error (    ErrorAtPos pos)
    -- actual fetch with modification : put tail cs
    (c:cs) -> Success (c :# (pos + 1, cs))

-- | error at current position
parseError :: Parser a
parseError = P $ ES \(p, _) -> Error $ ErrorAtPos p

instance Alternative Parser where
  empty = parseError
  P f <|> P g =
    P $ ES \s0 ->
      let r1 = runES f s0 in
      case r1 of
        Success s -> Success s
        -- it does not sutisfy <|> rule, but
        -- second error is more informative than
        -- error in the beginning of alternative
        -- (if there were messages as well as position...)
        Error _   -> runES g s0

-- | checks end of file
pEof :: Parser ()
pEof = P $ ES \s@(p, r) ->
  case r of
    [] -> Success (():# s)
    _  -> Error $ ErrorAtPos p

-- | parse expression from string
parseExpr :: String -> Except ParseError Expr
parseExpr = runP parseMain
  -- encapsulation
  where
    parseMain = parseAddSub
    parseAddSub = parseBop [('+',  Add), ('-', Sub)] parseMulDiv
    parseMulDiv = parseBop [('*',  Mul), ('/', Div)] parseAtom
    parseBop chr2ctor smaller = do
      lft <- smaller
      let
        try :: Parser (Expr -> Prim Expr)
        try = do
          c <- fetchCharIf2 (`elem` map fst chr2ctor)
          let matched = head $ filter (\x -> fst x == c) chr2ctor
          flip (snd matched) <$> smaller
      (foldl' (\x f -> Op $ f x) lft <$> some try) <|> return lft
    parseNum = do
      -- this function may be easier to implement without `optional`
      -- b/c
      -- > fromMaybe a <$> some b`
      -- ===
      -- > b <|> return a
      -- which is more readable, but we were asked
      -- to use this functions
      skipWs
      Val . toRealFloat . read <$>
        -- read \d+ (\.\d+)? as string
        liftM2 (++)
          -- read whole part
          (some (mfilter isDigit pChar))
          -- read frac part, defaulting to ""
          (fromMaybe "" <$>
            -- try to read frac part
            optional
              -- concatenate point and frac
              (liftM2 (:)
                -- read '.'
                (fetchCharIf (== '.'))
                (some (mfilter isDigit pChar))))
    parseParen = fetchChar2 '(' *> parseMain <* fetchChar2 ')'
    parseAtom = parseParen <|> parseNum
    -- | read char if and only predicate f satisfies
    fetchCharIf f = do
      p <- pChar
      unless (f p) parseError
      return p
    skipWs = many (fetchCharIf isSpace)
    -- | skip2 whitespace before
    pChar2 :: Parser Char
    pChar2 = do
      skipWs
      pChar
    fetchCharIf2 f = do
      p <- pChar2
      unless (f p) parseError
      return p
    fetchChar2 c = fetchCharIf2 (== c)

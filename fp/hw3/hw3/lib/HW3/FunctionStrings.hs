module HW3.FunctionStrings where

import Data.Char (isUpper, toLower)
import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NonEmpty

import HW3.Base

allFunctions :: [(String, HiFun)]
allFunctions =
  [("cd", HiFunChDir), ("mkdir", HiFunMkDir)]
  ++ filter
      (not . flip elem ["ch-dir", "mk-dir"] . fst) -- this use different convention
      [(gen x, x) | x <- [minBound..maxBound]]
  where
    gen :: HiFun -> String
    gen x = intercalate "-" $ NonEmpty.tail $ splitCap $ drop 5 $ show x
    splitCap :: String -> NonEmpty String
    splitCap [] = [] :| []
    splitCap (x:xs)
      | isUpper x = [] :| (toLower x : wordTail) : other
      | otherwise = (x : wordTail) :| other
      where
        wordTail :| other = splitCap xs

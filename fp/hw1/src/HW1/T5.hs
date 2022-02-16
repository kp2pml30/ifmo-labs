module HW1.T5
  ( splitOn
  , joinWith
  ) where

import Data.List.NonEmpty (NonEmpty ((:|)), (<|))
import qualified Data.List.NonEmpty as NE

splitOn :: Eq a => a -> [a] -> NonEmpty [a]
splitOn sep lst =
  let (h, t) = span (/= sep) lst in
  case t of
    [] -> h :| [] -- NE.singleton h
    _  -> h <| splitOn sep (tail t)

joinWith :: a -> NonEmpty [a] -> [a]
joinWith sep (a :| lst) = a ++ concatMap (sep:) lst

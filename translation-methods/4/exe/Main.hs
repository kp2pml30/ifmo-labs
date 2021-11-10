{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import YPar.Par

import qualified Data.Text.IO as TextIO
import System.IO (hPutStrLn, stderr)
import System.Exit (exitFailure)
import Data.String (IsString(..))

main = do
	s <- getContents
	case processGrammar <$> parseGrammar (fromString s) of
		Left p -> hPutStrLn stderr ("Error occured " ++ show p) >> exitFailure
		Right r -> TextIO.putStrLn r

module Main where

import qualified Data.Set as Set
import Prettyprinter
import Prettyprinter.Render.Terminal
import System.Console.Haskeline
import Text.Megaparsec.Error

import Control.Monad.Identity
import Control.Monad.Trans
import HW3.Action
import HW3.Base
import HW3.Evaluator
import HW3.Parser
import HW3.Pretty

mySettings :: Settings IO
mySettings = defaultSettings { historyFile = Just "./.hihistory" }

instance HiMonad Identity where
  runAction = const $ return HiValueNull

loop :: InputT IO ()
loop = do
  input <- handleInterrupt (return Nothing) $ Just <$> getInputLine "hi> "
  case input of
    Nothing -> do
      outputStrLn "Interrupt"
      loop
    Just Nothing -> outputStrLn "Quit"
    Just (Just s) -> do
      case parse s of
        Left err -> outputStrLn $ errorBundlePretty err
        Right expr -> do
          res <- liftIO $ runHIO (eval expr) $ Set.fromList [minBound..maxBound]
          case res of
            Left err -> outputStrLn $ show err
            Right result -> do
              lift $ putDoc $ prettyValue result <> pretty "\n"

      loop

main :: IO ()
main = do
  runInputT mySettings $ withInterrupt loop

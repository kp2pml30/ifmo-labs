import Numeric (showHex, showIntAtBase)
import Data.Char (intToDigit)
import qualified Data.Map as Map
import Data.Foldable

toBin x = showIntAtBase 2 intToDigit x ""

main = do
    s <- getContents
    let
        wd = map words $ lines s
        n = map (toBin . (read :: String -> Int) . head . tail) wd
        w = map (head . head) wd
        mp = Map.fromList $ zip w n
        key = "I_Like_"
    mapM_ (\(k, v) -> putStrLn $ [k] ++ " " ++ show (length v) ++ "\t" ++ v) (Map.toList mp)
    -- print $ take 16 $ map toBin [1..]
    -- putStrLn "????"
    -- putStrLn $ foldMap (mp Map.!) key
    -- putStrLn $ foldl' (\x y -> x ++ " " ++ y) "" $ map (mp Map.!) key
    
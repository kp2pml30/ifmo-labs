import Numeric (showHex, showIntAtBase)
import Data.Char (intToDigit)
import qualified Data.Map as Map
import Data.Foldable
import Data.List
import Control.Monad

toBin x = showIntAtBase 2 intToDigit x ""

main = do
    s <- getContents
    let
        wd = map words $ lines s
        n = map (head . tail . tail) wd
        w = map (head . head) wd
        mp = zip n w
        key = "I_Like_"
    let
        spin s = do
            let (Just t) = findIndex (== True) (map (all (== True) . zipWith (==) s) n)
            
            let k = mp !! t
            putStr [snd k]
            let ns = drop (length $ fst k) s
            when (ns /= "") (spin ns)
    spin "0000000011000110101100101000100100000111000110011001001111011000011110000110001011011111111010101000011011101101011100110001000001100100000111010101110000110011111010100010000101110100101110011000001010110111100001101110110101011001000001011101100000100100000011111011101000000100110000100011111011001000011001010100101011100110"
    return ()
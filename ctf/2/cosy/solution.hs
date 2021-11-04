import Data.List
import Data.Char
import qualified Data.Map as Map
import Data.Map ((!))

bmap c =
	if c <= 25 then c + 97 else
	if c <= 35 then c + 22 else
	if c == 36 then ord '{' else
	if c == 37 then ord '}' else
	if c == 38 then ord '_' else
	undefined


bz :: Double -> Int
bz x = floor $ x * 10000

lst :: [Int]
lst = [0..38]

armap x = (fromIntegral x) * 3.141 / 180.0

sines = Map.fromList [(bz $ sin $ armap x, x) | x <- lst]
cosines = Map.fromList [(bz $ cos $ armap x, x) | x <- lst]

doJob [] = []
doJob [x] = [sines ! x]
doJob (x:y:xs) = (sines ! x) : (cosines ! y) : doJob xs

main = do
	-- print sines
	-- print cosines
	let
		nums :: [Int]
		nums = map read $ words "3089 9659 174 9993 3255 9961 5876 8910 6155 9986 4382 7880 1218 8660 3255 8746 6155 9781 4999 9455 1218 7987"
	putStrLn $ map (chr . bmap) $ doJob nums
import Data.Bits
import Data.Char

foo1 = id
foo2 = xor 255
foo3 a = (a + 17) `mod` 256
foo4 a = (a - 23 + 256) `mod` 256

main = do
	let
		fs :: [Int -> Int]
		fs = [foo1, foo2, foo3, foo4, foo3, foo2, foo3, foo4, foo2, foo1, foo4, foo1, foo3, foo2, foo1, foo4, foo1, foo2, foo3, foo4, foo3, foo2, foo3, foo4, foo2, foo1, foo4, foo1, foo3]
		nums = [115, 143, 81, 122, 99, 153, 106, 127, 207, 119, 118, 100, 32, 155, 95, 144, 48, 138, 78, 131, 32, 148, 34, 118, 139, 104, 75, 116, 108, 0]
	putStrLn $ map chr $ zipWith ($) fs nums

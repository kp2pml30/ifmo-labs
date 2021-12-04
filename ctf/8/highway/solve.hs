import System.IO 

cnt _ [] = []

cnt a (x:y:xs)
	| x == y = cnt (a + 1) (y:xs)
	| x /= y = a : cnt 0 xs

cnt _ l = error $ show l

base64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"

main = do
	f <- lines <$> readFile "trace-filter"
	let res = cnt 0 f
	print res
	putStrLn $ map (base64 !!) res
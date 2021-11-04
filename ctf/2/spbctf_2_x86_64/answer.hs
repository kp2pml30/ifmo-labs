import Data.List
import Data.Char

primes = 2:seive [3, 5 ..]
	where
		seive (h:t) = h : [x | x <- t, x `mod` h /= 0]

factor x =
	hellp x primes []
	where
		hellp 1 _ a = a
		hellp x pl@(p:pt) a 
			| x `mod` p == 0 = hellp (x `div` p) pl (p:a)
			| otherwise = hellp x pt a

commonPart [] _ = []
commonPart _ [] = []
commonPart l1@(h1:t1) l2@(h2:t2)
	| h1 == h2 = h1 : commonPart t1 t2
	| h1 < h2  = commonPart l1 t2
	| h2 < h1  = commonPart t1 l2

doJob [] = []
doJob (a:b:t) =
	let res = product $ commonPart (factor a) (factor b) in
	res : doJob t

main = do
	let
		nums :: [Int]
		nums = map read $ words "497 1207 1273 871 476 884 1615 475 2233 231 505 1919 190 2755 231 561"
	print $ map chr $ doJob nums
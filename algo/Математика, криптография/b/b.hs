import Data.Int
import qualified Data.Set as Set

primes :: (Integral int) => [int]
primes = sieve [2..] where
    sieve (p:t) = p : sieve [x | x <- t, x `mod` p > 0]

type ImplementationInt = Integer

str2Int = read :: String -> ImplementationInt
str2IntLst = map str2Int

randNums :: Integral int => [int]
randNums = [710030073967877738, 768110093676275131, 73992102846919534, 250637484270206308, 335693667086925794, 229507813963619087, 628134919844032554, 314867564769697933, 452091854752369112, 56381856782254569, 706060261138607161, 994667377929795098, 957958795538333353, 877541526298565026]

mypow :: (Integral int) => int -> int -> int -> int
mypow _ 0 _ = 1
mypow b' e md =
    let b = b' `mod` md in
    let ne = e `div` 2 in
    ((mypow (b ^ 2) ne md) * if (e `mod` 2) == 1 then b else 1) `mod` md

fermaTest :: (Integral int) => int -> int -> Bool
fermaTest n rnd =
    let n' = n - 1 in
    let rnd' = (rnd `mod` n') + 1 in
    if (gcd rnd' n) /= 1
    then False
    else (mypow rnd' n' n) == 1

fermaTestAll :: (Integral int) => int -> Bool
fermaTestAll x = all (fermaTest x) randNums

chopr0 x
    | x == 0 = undefined
    | x `mod` 2 == 0 = chopr0 (x `div` 2)
    | otherwise = x

mapRand s e r = (r `mod` (e - s)) + s

millerRabin' d x n =
    if d == n - 1
    then False
    else let nx = x * x `mod` n in
    let nd = d * 2 in
    if nx == 1 then False
    else if nx == n - 1 then True
    else millerRabin' nd nx n

millerRabin d n rnd =
    let a = mapRand 2 (n - 2) rnd in
    if gcd n a /= 1 then False else
    let x = mypow a d n in
    if x == 1 || x == n - 1 then True else
    millerRabin' d x n

millerRabinAll n =
    let d = chopr0 (n - 1) in
    all (millerRabin d n) randNums

testX :: (Integral int) => int -> Bool
testX x =
    if x <= 1 then False else
    if x == 2 then True else
    if x `mod` 2 == 0 then False else
    if x < 6 then True else
    millerRabinAll x -- && (fermaTestAll x) -- && ((factors x) == [x])

trueFalseMapper True = "YES"
trueFalseMapper False = "NO"

main :: IO ()
{-
main = do
    mapM_ print $ filter testX [5..100]
-}    
main = do
    line <- getLine
    let n = read line :: Int
    rest <- getContents
    let nums = str2IntLst $ take n $ lines rest
    let answers = map testX nums
    mapM_ putStrLn $ map trueFalseMapper answers

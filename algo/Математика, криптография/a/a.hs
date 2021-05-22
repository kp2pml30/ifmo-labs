primes :: [Int]
primes = sieve [2..] where
    sieve (p:t) = p : sieve [x | x <- t, x `mod` p > 0]

factorsImpl _ 1 = []
factorsImpl i x = 
    if curp ^ 2 > x
    then [x]
    else if (x `mod` curp) == 0
    then [curp] ++ factorsImpl i (x `div` curp)
    else factorsImpl (i + 1) x
    where curp = primes!!i
factors = factorsImpl 0

main = do
    line <- getLine
    let a = read line :: Int
    putStrLn $ unwords . map show $ factors a
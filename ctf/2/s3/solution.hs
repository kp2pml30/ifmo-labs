import Data.Char
import Data.List

p (x,w) c = ((c + 1) * x  `mod` 256, (chr c):w)

chrs = map ord $ ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ "!@#$%^&*()_+|\\[]{};':\",./<>?"

main =
	check [(117, "?")]
	where
		-- check :: [Int] -> IO ()
		check l = do
			let n = [p x y | x <- l, y <- chrs]
			let r = find (\(a,_) -> a == 118) n
			maybe (check n) (putStrLn . snd) r
	
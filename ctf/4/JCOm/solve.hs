import Data.Int
import Data.List

l :: [Int32]
l = [1, 1] ++ zipWith (\a b -> a + b + 1) l (tail l)

main = do
	print $ find (\(_,a) -> a == 866988873) $ zip [0..] l
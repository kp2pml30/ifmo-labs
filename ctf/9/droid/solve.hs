import qualified Data.Set as Set

imDec :: [Int]
imDec = [35,35,35,35,35,35,35,35,35,35,35,35,35,35,35,35,35,35,35,35,35,35,35,111,32,32,32,32,35,32,35,32,35,32,32,32,32,32,32,32,32,32,35,35,35,32,35,32,35,35,35,32,35,32,35,32,35,35,35,32,35,35,35,32,35,35,35,32,35,35,32,32,32,32,32,32,32,32,32,32,32,32,32,35,32,35,35,35,35,32,35,32,32,32,35,35,35,35,35,32,35,32,35,35,35,32,35,35,35,35,35,32,35,32,35,32,32,32,32,32,32,35,35,32,32,32,35,32,32,32,35,35,35,32,35,32,35,35,35,35,35,35,32,35,35,35,35,35,35,35,35,35,35,35,35,32,32,32,35,32,32,32,32,32,32,32,32,32,32,32,32,35,32,32,120,35,35,32,35,35,35,32,35,32,35,35,35,35,35,35,35,35,35,35,32,35,35,35,35,32,32,32,35,32,35,32,32,32,32,32,32,32,32,32,32,32,32,32,35,35,35,35,35,35,35,35,35,35,35,35,35,35,35,35,35,35,35,35,35,35,35,35]

allowedLst :: [Int]
allowedLst = map snd $ filter (\(i,_) -> i == 32 || i == 120 || i == 111) $ zip imDec [0..]

allowed = Set.fromList allowedLst

firstJust :: [Maybe a] -> Maybe a
firstJust [] = Nothing
firstJust (Just x : xs) = Just x
firstJust (Nothing : xs) = firstJust xs

elseNothing :: Bool -> Maybe a -> Maybe a
elseNothing True x = x
elseNothing False _ = Nothing

dfs :: Int -> Int -> Int -> [Char] -> Maybe [Char]
dfs m p len path =
	if len > 41 then Nothing else
	let ind = m * 22 + p in
	if ind == 174
	then Just path
	else if not $ Set.member ind allowed
	then Nothing
	else
		firstJust
			[ elseNothing (head path /= 'U') $ dfs (m + 1) p (len + 1) ('D':path)
			, elseNothing (head path /= 'D') $ dfs (m - 1) p (len + 1) ('U':path)
			, elseNothing (head path /= 'L') $ dfs m (p + 1) (len + 1) ('R':path)
			, elseNothing (head path /= 'R') $ dfs m (p - 1) (len + 1) ('L':path)
			]

main = do
	print $ tail . reverse <$> dfs 1 1 0 ['?']

-- map (\i -> chr $ (i + 256) `mod` 256) -- insert your decode 2 here
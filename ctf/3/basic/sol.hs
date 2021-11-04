posOf c [] = error (c:" not found")
posOf c (a:t)
	| c == a = 0
	| otherwise = 1 + posOf c t

correct = "IYYTIR27GE2V6QSBKNCV6T2GL5AU4WIK"
order = "ABCDEFGHIJKLMNOPQRSTUVWXYZ234567"

main = do
	print $ map (flip posOf $ order) correct 

-- [8,24,24,19,8,17,26,31,6,4,26,21,30,16,18,1,10,13,2,21,30,19,26,6,11,29,0,20,28,22,8,10]
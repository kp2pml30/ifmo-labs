module Obfuscation.Obf where

import Obfuscation.Expr
import Data.Foldable

mergeDepthes (a, b) (x, y) = (a + x, b `max` y)

calculateVarDepthes :: [Statement a] -> Int
calculateVarDepthes  lst = uncurry (+) $ foldl' mergeDepthes (0, 0) $ map calculateVarDepth lst

calculateVarDepth :: Statement a -> (Int, Int)
calculateVarDepth Decl {} = (1, 0)
calculateVarDepth (SIf _ t e) = (0, calculateVarDepthes t `max` maybe 0 calculateVarDepthes e)
calculateVarDepth _ = (0, 0)

funcDepth (Function _ _ a s) = length a + calculateVarDepthes s

maxDepth lst = foldl' max 0 $ map funcDepth lst

mkName l i = (if i `mod` 2 == 0 then 'I' else 'O') : h l (i `div` 2)
	where
		h 0 _ = []
		h l i = (case i `mod` 4 of
			0 -> 'I'
			1 -> '1'
			2 -> 'O'
			3 -> '0'
			_ -> undefined) : h (l - 1) (i `div` 4)

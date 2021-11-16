import Control.Monad.State
import Control.Monad.Reader
import qualified Data.Map as Map
import Data.Foldable
import Data.Char

type Graph = Map.Map Int ([Int], [Int])

data Cell = Unknown | Zero | One deriving (Eq)

instance Show Cell where
	show Zero = "0"
	show One = "1"
	show _ = "?"

flipCell Zero = One
flipCell One = Zero

type FullState = Map.Map Int Cell
type MyMonadA = ReaderT Graph (State FullState)
type MyMonad = MyMonadA ()

trace :: Cell -> Int -> MyMonad
trace c i = do
	prev <- lift $ gets (Map.! i)
	case prev of
		Unknown -> do
			lift $ modify $ Map.insert i c
			(same, diff) <- reader (Map.! i)
			mapM_ (trace c) same
			mapM_ (trace $ flipCell c) diff
		x
			| x /= c -> error "whaaaaat"
			| otherwise -> return ()

doJob :: Int -> MyMonad
doJob 32 = return ()
doJob i = do
	prev <- lift $ gets (Map.! i)
	case prev of
		Unknown -> trace (if not $ even i then Zero else One) i
		_ -> return ()
	doJob $ i + 1
	-- return ()

mpCell :: Cell -> Int
mpCell One = 1
mpCell Zero = 0

sumCell a b = a * 2 + mpCell b

process [] = []
process lst = foldl' sumCell 0 (take 8 lst) : process (drop 8 lst)

main = do
	let
		n1 :: [Int]
		n1 = reverse $ [0..31]
		n2 :: [Int]
		n2 = reverse $ take 32 $ drop (32 - 14) $ cycle [0..31]
		xorResults :: [Bool]
		xorResults = map (\c -> read [c] /= 0) $ "01011001001101100001001100100011"
		zipped = zip3 n1 n2 xorResults
		emptyGraph :: Graph
		emptyGraph = foldl'
			(\m k -> Map.insert k ([], []) m)
			Map.empty
			n1
		graph = foldl'
			(\gr (v1, v2, xorRes) ->
				let adj i (a, b) = if xorRes then (a, i:b) else (i:a, b) in
				Map.adjust (adj v1) v2 $ Map.adjust (adj v2) v1 gr)
			emptyGraph zipped
		initCells = Map.fromList $ zip [0..] $ take 32 $ repeat Unknown
	print zipped
	let result = execState (runReaderT (doJob 0) graph) initCells
	let resultCells = map snd $ Map.toDescList result -- map (result Map.!) n1
	let prn = foldMap show resultCells
	print $ prn
	print $ reverse $ map chr $ process $ resultCells
	putStrLn "reversed"
	print $ reverse $ prn
	print $ reverse $ map chr $ process $ reverse resultCells
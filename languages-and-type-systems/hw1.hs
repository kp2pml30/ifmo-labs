import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad

data Expr
	= Lam String Expr
	| App Expr Expr
	| Var String
	deriving (Eq)

wrp True x = "(" ++ x ++ ")"
wrp False x = x

isLam o = case o of
	Lam _ _ -> True
	_ -> False

isVar o = case o of
	Var _ -> True
	_ -> False

dmp :: Expr -> String
dmp (Var x) = x
dmp (App x y) = (wrp (isLam x) $ dmp x) ++ " space " ++ (wrp (not $ isVar y) $ dmp y)
dmp (Lam n x) = "lambda " ++ n ++ " . space " ++ dmp x

dmpDeb :: Map.Map String Int -> Int -> Expr -> String
dmpDeb mp dep (Var x) =
	case Map.lookup x mp of
		Nothing -> x
		Just a -> show $ dep - 1 - a
dmpDeb mp dep (Lam n e) =
	"lambda " ++ dmpDeb (Map.insert n dep mp) (dep + 1) e
dmpDeb mp dep (App x y) =
	(wrp (isLam x) $ dmpDeb mp dep x) ++ " space " ++ (wrp (not $ isVar y) $ dmpDeb mp dep y)

infixl 4 `App`

rename :: Set.Set String -> Map.Map String String -> Expr -> (Set.Set String, Expr)
rename f m (Var x) = (f, Var (maybe x id $ Map.lookup x m))
rename f m (App x y) =
	let (f', x') = rename f m x in
	let (f'', y') = rename f' m y in
	(f'', App x' y')
rename f m (Lam v e) =
	let newName = if Set.member v f then v else Set.elemAt 0 f in
	let (f', e') = rename (Set.delete newName f) (Map.insert v newName m) e in
	(f', Lam newName e')

repl fr to (Var x) | x == fr = to
repl fr to (Var x) | x /= fr = Var x
repl fr to (Lam n e) | n /= fr = Lam n $ repl fr to e
repl fr to (Lam n e) | n == fr = undefined
repl fr to (App x y) = App (repl fr to x) (repl fr to y)

isValue (Var _) = True
isValue (Lam _ _) = True
isValue _ = False

step (Var _) = Nothing
step (Lam _ _) = Nothing
step (App x y) =
	case step x of
		Nothing ->
			case App x <$> (if isValue x then step y else Nothing) of
				Just o -> Just o
				Nothing ->
					case x of
						(Lam r e) -> Just $ repl r y e
						_ -> Nothing
		Just a -> Just $ App a y

task expr = do
	putStrLn $ "== $" ++ dmp expr ++ "$"
	spin expr
	where
		newVars = Set.fromList [x : [] | x <- ['a' .. 'z']] Set.\\ Set.fromList ["x", "y", "z"]
		spin e' = do
			putStrLn $ "+ $" ++ dmp e' ++ "$"
			let e = snd $ rename newVars Map.empty e'
			when (e /= e') $ do
				putStrLn $ "  - $alpha$ equiv: $" ++ (dmp e) ++ "$"
			putStrLn $ "  - de Bruijn $" ++ (dmpDeb Map.empty 0 e) ++ "$"
			case step e of
				Just e -> spin e
				Nothing -> pure ()

main :: IO ()
main = do
	let x = Var "x"
	let y = Var "y"
	let z = Var "z"
	-- (λx. λy. λz. y x) (λy. y) (λy. z)
	task $ (Lam "x" $ Lam "y" $ Lam "z" $ y `App` x) `App` (Lam "y" y) `App` (Lam "y" z)
	-- (λx. λy. (λz. x) y) (λy. y) (λy. z)
	task $ (Lam "x" $ Lam "y" $ (Lam "z" x) `App` y) `App` (Lam "y" y) `App` (Lam "y" z)
	-- (λx. λy. λz. x z y) (λy. λx. x) z x
	task $ (Lam "x" $ Lam "y" $ Lam "z" x `App` z `App` y) `App` (Lam "y" $ Lam "x" x) `App` z `App` x
	-- (λx. λy. x (x y)) (λy. λz. y (y z)) (λz. x z) y
	task $ (Lam "x" $ Lam "y" $ x `App` (x `App` y)) `App` (Lam "y" $ Lam "z" $ y `App` (y `App` z)) `App` (Lam "z" $ x `App` z) `App` y

module Task2Expr (Expr(..), shB, expr2Dot) where

import qualified Data.Sequence as Seq
import Data.Sequence (Seq)
import Control.Monad.State
import Data.Foldable (toList)

data Expr
	= Not { expr :: Expr }
	| Minus { lexpr :: Expr, rexpr :: Expr }
	| And { lexpr :: Expr, rexpr :: Expr }
	| Or { lexpr :: Expr, rexpr :: Expr }
	| Xor { lexpr :: Expr, rexpr :: Expr }
	| In { lexpr :: Expr, rexpr :: Expr }
	| Name { name :: String }
	deriving (Eq)

instance Show Expr where
	show Not {..} = "!" ++ show expr
	show e@Minus {} = shB "-" e
	show e@And {} = shB "&" e
	show e@Or {} = shB "|" e
	show e@Xor {} = shB "^" e
	show e@In {} = shB "∈" e
	show Name{..} = name

data MyState = MyState { nId :: Int, ans :: Seq Char }

type ST a = State MyState a

s2s = Seq.fromList

append :: Seq Char -> ST ()
append a = do
	modify \s@MyState { ans } -> s { ans = ans <> a }

mkId :: ST (Seq Char)
mkId = do
	prev <- gets nId
	modify (\s -> s { nId = prev + 1 })
	return $ s2s "v" <> s2s (show prev)

shwD :: Expr -> ST (Seq Char)
shwD Name { name } = do
	i <- mkId
	append $ i <> s2s "[shape=box,label=\"" <> s2s name <> s2s "\"];"
	return i
shwD Not { expr } = do
	i <- mkId
	nxt <- shwD expr
	append $ i <> s2s "[shape=circle,label=\"not\"];"
	append $ i <> s2s "->" <> nxt <> s2s ";"
	return i
shwD e@Minus {} = mkBop e "-"
shwD e@And {} = mkBop e "and"
shwD e@Or {} = mkBop e "or"
shwD e@Xor {} = mkBop e "xor"
shwD e@In {} = mkBop e "in"

mkBop e s = do
	i <- mkId
	nl <- shwD $ lexpr e
	nr <- shwD $ rexpr e
	append $ i <> s2s "[shape=circle,label=\"" <> s2s s <> s2s "\"];"
	append $ i <> s2s "->" <> nl <> s2s ";"
	append $ i <> s2s "->" <> nr <> s2s ";"
	return i


expr2Dot :: Expr -> String
expr2Dot e = toList $ s2s "digraph T {" <> ans (execState (shwD e) (MyState 0 Seq.empty)) <> s2s "}"

shB c e = "(" ++ show (lexpr e) ++ c ++ show (rexpr e) ++ ")"

{-# LANGUAGE QuasiQuotes, TemplateHaskell #-}

module Pysets.TH (deriveIs) where

import Language.Haskell.TH
import Data.Maybe

fetchNameE :: Char -> String -> Maybe String
fetchNameE _ [] = Nothing
fetchNameE x (a:xs)
	| a == x    = Just $ fromMaybe xs $ fetchNameE x xs
	| otherwise = fetchNameE x xs

fetchName c x = fromMaybe x (fetchNameE c x)

getName :: Con -> Name
getName (RecC n _) = n
getName (NormalC n _) = n
getName _ = undefined

deriveIs :: Name -> Q [Dec]
deriveIs n = do
	d <- reify n
	case d of
		TyConI (DataD _ _ _ _ con _) -> mapM genIs con
		_ -> error $ "not a declaration " ++ fetchName '.' (show n)
	where
		genIs a = do
			true <- runQ [e|True|]
			false <- runQ [e|False|]
			let name = mkName $ "is" ++ fetchName '.' (show $ getName a)
			return $ FunD name [Clause [RecP (getName a) []] (NormalB true) [], Clause [WildP] (NormalB false) []]

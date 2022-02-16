{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE TemplateHaskell #-}

{- | Code in this module generates boilerplate code for checking types.
 - First experience with TH
 -}
module HW3.Internal.TH where

import Language.Haskell.TH

import qualified Data.Map as Map

import HW3.Base
import HW3.Internal.Eval

{- three following functions ensure that types are not aliases -}

joinType :: Type -> Q Type
joinType = \case
  ConT t -> fullReify t
  s      -> return s

decToType :: Dec -> Q Type
decToType = \case
  TySynD _ _ s      -> joinType s
  DataD _ n _ _ _ _ -> return $ ConT n
  err               -> error $ show err

fullReify :: Name -> Q Type
fullReify n =
  reify n >>= \case
    TyConI d -> decToType d
    err      -> error $ show err

-- | map of all types to constructors (for better code matching)
type2Name :: Q (Map.Map Type Name)
type2Name = do
  TyConI hiValue <- reify ''HiValue
  let DataD _ _ _ _ cons _ = hiValue
  mappedCtors <- mapM
    (\(NormalC n ty) -> do
      case ty of
        [(_, t)] -> do
          trueT <- joinType t
          return [(trueT, n)]
        _ -> return []
    )
    cons
  return $ Map.fromList $ concat mappedCtors

-- | makes parser for type
-- which throws on type mismatch
-- e.g. (evalTy ''Bool) :: HiValue -> EvalMonad hi Bool
evalTy :: Name -> Q Exp
evalTy tyName = do
  ty <- fullReify tyName
  mism <- NormalB <$> runQ [e|throwArgTypeMismatch|]
  t2Name <- type2Name
  x <- newName "r"
  retE <- [e|return|]
  let mkAppl = NormalB . AppE retE . VarE
  case Map.lookup ty t2Name of
    Nothing -> error $ "can't find " ++ show ty ++ " in typemap " ++ show t2Name
    Just c -> return $ LamCaseE
      [ Match (ConP c [VarP x]) (mkAppl x) []
      , Match WildP mism []
      ]

{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

module HW3.Evaluator (eval) where

import Codec.Compression.Zlib
import Codec.Serialise
import Control.Applicative
import Control.Monad
import Data.Bifunctor
import Data.Either
import Data.Foldable
import qualified Data.Map as Map
import Data.Maybe
import Data.Ratio
import Data.Semigroup (stimes)
import Data.Tuple (swap)
import Text.Read (readMaybe)

import Data.ByteString (ByteString)
import qualified Data.ByteString as ByteString
import qualified Data.ByteString.Lazy as BSL
import Data.Function (on)
import qualified Data.Sequence as Seq
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TextEnc
import Data.Time (UTCTime)
import Data.Time.Clock (addUTCTime, diffUTCTime)

import HW3.AbstractContainer
import HW3.Base
import HW3.Internal.Eval
import HW3.Internal.TH

ratToInteger :: HiMonad him => Rational -> EvalMonad him Integer
ratToInteger rat = case denominator rat of
  1 -> return $ numerator rat
  _ -> throwArgTypeMismatch

integerToInt :: HiMonad him => Integer -> EvalMonad him Int
integerToInt x = do
  let
    cast :: Int -> Integer
    cast = fromIntegral
  when (x < cast minBound) $ throwHi HiErrorInvalidArgument
  when (x > cast maxBound) $ throwHi HiErrorInvalidArgument
  return $ fromInteger x

-- | evaluate expression with default on null
evalNullDflt :: HiMonad him => a -> (HiValue -> EvalMonad him a) -> HiExpr -> EvalMonad him a
evalNullDflt onNull mapper e = do
  ev <- evalE e
  case ev of
    HiValueNull -> return onNull
    _           -> mapper ev

-- | common code for all binary operators
-- is not strict
evalBopEx
  :: (HiValueWrap r, HiMonad him)
  => (HiValue -> EvalMonad him a) -- ^ unwrapper for left argument (e.g. type-checekr)
  -> (HiValue -> EvalMonad him b) -- ^ unwrapper for right argument
  -> (EvalMonad him a -> EvalMonad him b -> EvalMonad him r) -- ^ operator
  -> [HiExpr] -- ^ arguments list, exepects size 2, otherwise throws ArityError
  -> EvalMonad him HiValue
evalBopEx unwrapl unwrapr op [l, r] = wrapHi <$> ((evalE l >>= unwrapl) `op` (evalE r >>= unwrapr))
evalBopEx _ _ _ _                   = throwHi HiErrorArityMismatch

-- | same as evalBopEx, but with non-monadic arguments, left-to-right evaluation
evalBopM  :: (HiValueWrap r, HiMonad him)
  => (HiValue -> EvalMonad him a) -- ^ unwrapper for left argument (e.g. type-checekr)
  -> (HiValue -> EvalMonad him b) -- ^ unwrapper for right argument
  -> (a -> b -> EvalMonad him r) -- ^ operator
  -> [HiExpr] -- ^ arguments list, exepects size 2, otherwise throws ArityError
  -> EvalMonad him HiValue
evalBopM unwrapl unwrapr op = evalBopEx unwrapl unwrapr \lm rm -> join $ op <$> lm <*> rm

-- | same as evalBopEx, but with strict left-to-right evaluation
evalBop  :: (HiValueWrap r, HiMonad him)
  => (HiValue -> EvalMonad him a) -- ^ unwrapper for left argument (e.g. type-checekr)
  -> (HiValue -> EvalMonad him b) -- ^ unwrapper for right argument
  -> (a -> b -> r) -- ^ operator
  -> [HiExpr] -- ^ arguments list, exepects size 2, otherwise throws ArityError
  -> EvalMonad him HiValue
evalBop unwrapl unwrapr op = evalBopEx unwrapl unwrapr (liftM2 op)

-- | short version for operator of two rationals
evalRatBop :: HiMonad him => (Rational -> Rational -> Rational) -> [HiExpr] -> EvalMonad him HiValue
evalRatBop = join evalBop $(evalTy ''Rational)

-- | function that strictly evaluates exactly 2 arguments left-to-right
evalBopAny :: (HiMonad him, HiValueWrap wr) => (HiValue -> HiValue -> wr) -> [HiExpr] -> EvalMonad him HiValue
evalBopAny = join evalBop return

-- | common code for 1 argument functions
unaryFunction :: HiMonad him => (HiValueWrap w) => (HiExpr -> EvalMonad him w) -> [HiExpr] -> EvalMonad him HiValue
unaryFunction f [l] = wrapHi <$> f l
unaryFunction _ _   = throwHi HiErrorArityMismatch

-- | common code for 1 typed argument functions without overloading
unaryTypedM :: HiMonad him => (HiValueWrap r) => (HiValue -> EvalMonad him a) -> (a -> EvalMonad him r) -> [HiExpr] -> EvalMonad him HiValue
unaryTypedM typeMap f = unaryFunction \s -> evalE s >>= typeMap >>= f

-- | result is not monadic
unaryTyped :: HiMonad him => (HiValueWrap r) => (HiValue -> EvalMonad him a) -> (a -> r) -> [HiExpr] -> EvalMonad him HiValue
unaryTyped typeMap f = unaryTypedM typeMap (return . f)

-- | selects overload
-- note that it firstly strictly evaluates arguments
-- and than packs  them back into Expression
-- to have common code for other operators, e.g. || is lazy
--
-- we can't find type without evaluation b/c of `if` function
selectOverload :: HiMonad him => [[HiExpr] -> EvalMonad him HiValue] -> [HiExpr] -> EvalMonad him HiValue
selectOverload alt args = do
  eargs <- mapM (fmap HiExprValue . evalE) args
  foldl' (\p n -> p <|> n eargs) empty alt

-- | common code for container concatenation
evalContainerConcat :: HiMonad him => (HiValueWrap a, Semigroup a) => (HiValue -> EvalMonad him a) -> [HiExpr] -> EvalMonad him HiValue
evalContainerConcat reader = join evalBop reader (<>)

-- | common code for container * int
evalContainerTimes :: HiMonad him => (HiValueWrap a, Semigroup a) => (HiValue -> EvalMonad him a) -> [HiExpr] -> EvalMonad him HiValue
evalContainerTimes reader = evalBopM reader ($(evalTy ''Rational) >=> ratToInteger) \s c -> do
  when (c <= 0) (throwHi HiErrorInvalidArgument)
  return $ stimes c s

-- | common code for || and &&
{-
evalLogic
  :: HiMonad him
  => (HiValue -> EvalMonad him HiValue -> EvalMonad him HiValue)
  -> (HiValue -> EvalMonad him HiValue -> EvalMonad him HiValue)
  -> EvalMonad him HiValue
-}
evalLogic onFalse onTrue = join evalBopEx return \l r -> do
  le <- l
  case le of
    HiValueNull       -> onFalse le       r
    HiValueBool False -> onFalse le r
    _                 -> onTrue le r

-- | implementation of all built in function evaluation
-- evaluate Function
evalF :: forall him. HiMonad him => HiFun -> [HiExpr] -> EvalMonad him HiValue
{- numeric function -}
evalF HiFunAdd = selectOverload
  [ evalRatBop (+)
  , evalContainerConcat $(evalTy ''Text)
  , evalContainerConcat $(evalTy ''HiLst)
  , evalContainerConcat $(evalTy ''ByteString)
  , evalBop $(evalTy ''UTCTime) $(evalTy ''Rational) \t r -> fromRational r `addUTCTime` t
  ]
evalF HiFunSub = selectOverload
  [ evalRatBop (-)
  , join evalBop $(evalTy ''UTCTime) $ toRational .: diffUTCTime
  ]
evalF HiFunMul = selectOverload
  [ evalRatBop (*)
  , evalContainerTimes $(evalTy ''Text)
  , evalContainerTimes $(evalTy ''HiLst)
  , evalContainerTimes $(evalTy ''ByteString)
  ]
evalF HiFunDiv = selectOverload
  [ join evalBopM $(evalTy ''Rational) safeDiv
  , join evalBop  $(evalTy ''Text) (\l r -> l <> "/" <> r)
  ]
{- boolean function -}
evalF HiFunNot = unaryFunction \b -> not <$> (evalE b >>= $(evalTy ''Bool))
evalF HiFunAnd = evalLogic (\f _ -> return f) (\_ t -> t)
evalF HiFunOr = evalLogic (\_ t -> t) (\t _ -> return t)
{- Eq, Ord -}
evalF HiFunEquals = evalBopAny (==)
evalF HiFunNotEquals = evalBopAny (/=)
evalF HiFunLessThan = evalBopAny (<)
evalF HiFunNotLessThan = evalBopAny (>=)
evalF HiFunGreaterThan= evalBopAny (>)
evalF HiFunNotGreaterThan= evalBopAny (<=)
{- if -}
evalF HiFunIf = \case
  [c, t, f] -> do
    ce <- evalE c
    {-
    let
      isTrue = case ce of
        HiValueNull       -> False
        HiValueBool False -> False
        _                 -> True
    -}
    isTrue <- case ce of
      HiValueBool x -> return x
      _             -> throwHi HiErrorInvalidArgument
    evalE if isTrue then t else f
  _ -> throwHi HiErrorArityMismatch
{- strings -}
evalF HiFunTrim = unaryTyped $(evalTy ''Text) Text.strip
evalF HiFunToLower = unaryTyped $(evalTy ''Text) Text.toLower
evalF HiFunToUpper = unaryTyped $(evalTy ''Text) Text.toUpper
{- lists -}
evalF HiFunList = fmap (HiValueList . Seq.fromList) . mapM evalE
evalF HiFunRange = join evalBop $(evalTy ''Rational) \f t -> Seq.fromList $ map HiValueNumber [f..t]
{- containers -}
evalF HiFunFold =
  evalBopM
    (return . HiExprApply . HiExprValue)
    evalContainer
    \func c ->
      if acLen c == 0
      then return HiValueNull
      else
        let
          mkFold :: EvalMonad him HiValue -> HiValue -> EvalMonad him HiValue
          mkFold lM r = do
            l <- lM
            evalE (func $ HiExprValue <$> [l, r])
        in acFold mkFold (return $ acIndex c 0) (acDrop 1 c)
{- -- code for lists-only
case c of
  Seq.Empty -> return HiValueNull
  s ->
    foldl1
      (join .: liftM2 \a v ->
        evalE $ func (HiExprValue <$> [a, v]))
      (return <$> s)
-}
evalF HiFunLength = unaryTyped evalContainer acLen
evalF HiFunReverse = unaryTyped evalContainer acReverse
{- bytes -}
evalF HiFunPackBytes = unaryFunction \c -> evalE c >>= $(evalTy ''HiLst) >>= \lst -> do
  checked <- mapM check lst
  return $ HiValueBytes $ ByteString.pack $ toList checked
  where
    check cV = $(evalTy ''Rational) cV >>= ratToInteger >>= \c -> do
      when (c < 0 || c > 255) $ throwHi HiErrorInvalidArgument
      return $ fromIntegral c
evalF HiFunUnpackBytes  = unaryTyped $(evalTy ''ByteString) \bytes -> do
  Seq.fromList $ map (HiValueNumber . fromIntegral) $ ByteString.unpack bytes
evalF HiFunEncodeUtf8 = unaryTyped $(evalTy ''Text) TextEnc.encodeUtf8
evalF HiFunDecodeUtf8 = unaryTyped $(evalTy ''ByteString) $ either (const HiValueNull) wrapHi . TextEnc.decodeUtf8'
evalF HiFunZip = unaryTyped $(evalTy ''ByteString) $
  BSL.toStrict .
  compressWith defaultCompressParams { compressLevel = bestCompression } .
  BSL.fromStrict
evalF HiFunUnzip = unaryTyped $(evalTy ''ByteString) $ BSL.toStrict . decompress . BSL.fromStrict
evalF HiFunSerialise = unaryFunction $ fmap (BSL.toStrict . serialise) . evalE
evalF HiFunDeserialise = unaryTyped $(evalTy ''ByteString) $ fromRight HiValueNull . deserialiseOrFail . BSL.fromStrict
evalF HiFunRead = unaryTyped $(evalTy ''Text) $ HiActionRead . Text.unpack
evalF HiFunWrite = selectOverload
  [ evalBop $(evalTy ''Text) $(evalTy ''ByteString) $ HiActionWrite . Text.unpack -- first argument to pack, second to Write
  , evalBop $(evalTy ''Text) $(evalTy ''Text) $ \f c -> HiActionWrite (Text.unpack f) (TextEnc.encodeUtf8 c)
  ]
evalF HiFunMkDir = unaryTyped $(evalTy ''Text) $ HiActionMkDir . Text.unpack
evalF HiFunChDir = unaryTyped $(evalTy ''Text) $ HiActionChDir . Text.unpack
evalF HiExprRun = unaryTypedM $(evalTy ''HiAction) runAction
{- time -}
evalF HiFunParseTime = unaryTyped $(evalTy ''Text) $ maybe HiValueNull HiValueTime . readMaybe . Text.unpack
{- rand -}
evalF HiFunRand = join evalBopM ($(evalTy ''Rational) >=> ratToInteger >=> integerToInt) \l u -> do
  when (l > u) $ throwHi HiErrorInvalidArgument
  return $ wrapHi $ HiActionRand l u
{- echo -}
evalF HiFunEcho = unaryTyped $(evalTy ''Text) HiActionEcho
{- dictionaries -}
evalF HiFunCount = unaryTyped evalContainer \c ->
  let
    mp :: Map.Map HiValue Rational
    mp = acFold (\a e -> Map.insertWith (+) e 1 a) Map.empty c in
  wrapHi <$> mp
evalF HiFunKeys = unaryTyped $(evalTy ''HiDict) $ Seq.fromList . Map.keys
evalF HiFunValues = unaryTyped $(evalTy ''HiDict) $ Seq.fromList . Map.elems
evalF HiFunInvert = unaryTyped $(evalTy ''HiDict) \m ->
  let
    value2SingleKey :: [(HiValue, [HiValue])]
    value2SingleKey = fmap listSingleton . swap <$> Map.toList m in
  wrapHi . Seq.fromList <$> Map.fromListWith (++) value2SingleKey

-- | throws when denominator is zero
safeDiv :: HiMonad him => Rational -> Rational -> EvalMonad him Rational
safeDiv l r = do
  when (r == 0) $ throwHi HiErrorDivideByZero
  return $ l / r

-- | converts to an erased container
toContainer :: HiValue -> Maybe ErasedContainer
toContainer (HiValueString s) = Just $ ErasedContainer s
toContainer (HiValueList s)   = Just $ ErasedContainer s
toContainer (HiValueBytes s)  = Just $ ErasedContainer s
toContainer _                 = Nothing

-- | check that argument is a container
evalContainer :: HiMonad him => HiValue -> EvalMonad him ErasedContainer
evalContainer v = case toContainer v of
  Just c  -> return c
  Nothing -> throwHi HiErrorInvalidArgument

-- | common code for container indexing and slicing
containerIndexing :: HiMonad him => AbstractContainer c => c -> [HiExpr] -> EvalMonad him HiValue
containerIndexing t [i] = do
  ie :: Int <- fromInteger <$> (evalE i >>= $(evalTy ''Rational) >>= ratToInteger)
  if ie < 0 || ie >= acLen t
  then return HiValueNull
  else return $ t `acIndex` ie
containerIndexing t [l, r] = do
  let
    evalInt :: HiMonad him => HiValue -> EvalMonad him Int
    evalInt = $(evalTy ''Rational) >=> ratToInteger >=> (return . fromIntegral)
  let len = acLen t
  le :: Int <- evalNullDflt 0 evalInt l
  re :: Int <- evalNullDflt len evalInt r
  let
    checkFits x = do
      when (x < 0) $ throwHi HiErrorInvalidArgument
      -- when (x > len) $ throwHi HiErrorInvalidArgument
      -- ^ python slices do not throw, just return taken
  let mapF x = if x < 0 then x + len else x
  -- ^ not { (x + len) `mod` len } to avoid division by zero
  let lFinal = mapF le
  let rFinal = mapF re
  checkFits lFinal
  checkFits rFinal
  -- when (lFinal > rFinal) $ throwHi HiErrorInvalidArgument
  -- ^ python slices do not throw, just return "write.test"
  return $ wrapHi $ acTake (rFinal - lFinal) $ acDrop lFinal t
containerIndexing _ _ = throwHi HiErrorArityMismatch

-- | evaluate Expression function
evalE :: HiMonad him => HiExpr -> EvalMonad him HiValue
evalE (HiExprValue val) = return val
evalE (HiExprApply func args) = do
  f <- evalE func
  case f of
    HiValueFunction fu -> evalF fu args
    HiValueDict d -> unaryFunction
      (evalE >=> \a -> maybe (return HiValueNull) return $ Map.lookup a d)
      args
    s -> case toContainer s of
      Just c  -> containerIndexing  c args
      Nothing -> throwHi HiErrorInvalidFunction
evalE (HiExprDict d) =
  wrapHi . Map.fromList <$> mapM
    (uncurry (liftM2 (,) `on` evalE))
    d

-- | given interface function, which evaluates expression
eval :: HiMonad m => HiExpr -> m (Either HiError HiValue)
eval expr = first (fromMaybe HiErrorInvalidArgument) <$> runEval (evalE expr)

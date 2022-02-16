{-# LANGUAGE DeriveAnyClass, DeriveGeneric, CPP #-}
module HW3.Base where

import Codec.Serialise (Serialise)
import Data.ByteString (ByteString)
import Data.Map (Map)
import Data.Sequence (Seq)
import Data.Text (Text)
import Data.Time (UTCTime)
import Generics.Deriving (Generic)

#if MIN_VERSION_base(4,15,0)
import qualified Data.List
listSingleton :: a -> [a]
listSingleton = Data.List.singleton
#else
listSingleton :: a -> [a]
listSingleton = (:[])
#endif

-- | ready-to-execute actions
data HiAction
  = HiActionRead  FilePath
  | HiActionWrite FilePath ByteString
  | HiActionMkDir FilePath
  | HiActionChDir FilePath
  | HiActionCwd
  | HiActionNow
  | HiActionRand Int Int
  | HiActionEcho Text
  deriving (Eq, Ord, Show)
  deriving stock (Generic)
  deriving anyclass (Serialise)

class Monad m => HiMonad m where
  runAction :: HiAction -> m HiValue

data HiFun
  {- numeric -}
  = HiFunDiv
  | HiFunMul
  | HiFunAdd
  | HiFunSub
  {- boolean -}
  | HiFunNot
  | HiFunAnd
  | HiFunOr
  {- comp -}
  | HiFunLessThan
  | HiFunGreaterThan
  | HiFunEquals
  | HiFunNotLessThan
  | HiFunNotGreaterThan
  | HiFunNotEquals
  | HiFunIf
  {- str -}
  | HiFunLength
  | HiFunToUpper
  | HiFunToLower
  | HiFunReverse
  | HiFunTrim
  {- lists -}
  | HiFunList
  | HiFunRange
  | HiFunFold
  {- bytes -}
  | HiFunPackBytes
  | HiFunUnpackBytes
  | HiFunEncodeUtf8
  | HiFunDecodeUtf8
  | HiFunZip
  | HiFunUnzip
  | HiFunSerialise
  | HiFunDeserialise
  {- IO -}
  | HiFunRead
  | HiFunWrite
  | HiFunMkDir
  | HiFunChDir
  | HiExprRun
  {- time -}
  | HiFunParseTime
  | HiFunRand
  {- echo -}
  | HiFunEcho
  {- dictionaries -}
  | HiFunCount
  | HiFunKeys
  | HiFunValues
  | HiFunInvert
  deriving (Eq, Ord, Show, Bounded, Enum)
  deriving stock (Generic)
  deriving anyclass (Serialise)

data HiValue
  = HiValueNull
  | HiValueBool Bool
  | HiValueNumber Rational
  | HiValueString Text
  | HiValueFunction HiFun
  | HiValueList (Seq HiValue)
  | HiValueBytes ByteString
  | HiValueAction HiAction
  | HiValueTime UTCTime
  | HiValueDict (Map HiValue HiValue)
  deriving (Eq, Ord, Show)
  deriving stock (Generic)
  deriving anyclass (Serialise)

data HiExpr
  = HiExprValue HiValue
  | HiExprApply HiExpr [HiExpr]
  | HiExprDict [(HiExpr, HiExpr)]
  deriving (Show, Eq)

data HiError
  = HiErrorInvalidArgument
  | HiErrorInvalidFunction
  | HiErrorArityMismatch
  | HiErrorDivideByZero
  deriving (Eq, Show)

infixr 8 .:

(.:) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(.:) f g x = f . g x

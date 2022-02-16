{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies              #-}
module HW3.AbstractContainer where

import Data.ByteString (ByteString)
import qualified Data.ByteString as ByteString
import Data.Foldable
import Data.Map (Map)
import Data.Ratio
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Time (UTCTime)

import HW3.Base

-- | basic wrapper to reduce copypaste code
class HiValueWrap a where
  wrapHi :: a -> HiValue

instance HiValueWrap HiValue where
  wrapHi = id

instance (a ~ Integer) => HiValueWrap (Ratio a) where
  wrapHi = HiValueNumber

instance HiValueWrap Int where
  wrapHi = HiValueNumber . fromIntegral

instance HiValueWrap Bool where
  wrapHi = HiValueBool

instance HiValueWrap Text where
  wrapHi = HiValueString

instance (a ~ HiValue) => HiValueWrap (Seq a) where
  wrapHi = HiValueList

instance (a ~ HiValue) => HiValueWrap [a] where
  wrapHi = wrapHi . Seq.fromList

instance HiValueWrap ByteString where
  wrapHi = HiValueBytes

instance HiValueWrap HiAction where
  wrapHi = HiValueAction

instance HiValueWrap UTCTime where
  wrapHi = HiValueTime

instance (k ~ HiValue, v ~ HiValue) => HiValueWrap (Map k v) where
  wrapHi = HiValueDict

-- common code for lists and strings
-- not via [mono]foldable to preserve complexity
class HiValueWrap c => AbstractContainer c where
  acLen :: c -> Int
  acTake :: Int -> c -> c
  acDrop :: Int -> c -> c
  acIndex :: c -> Int -> HiValue
  acReverse :: c -> c
  -- | left strict fold
  acFold :: (a -> HiValue -> a) -> a -> c -> a
  acFold f s c = foldl' (\a i -> f a $ c `acIndex` i) s [0..acLen c - 1]
  {-# MINIMAL acLen, acTake, acDrop, acIndex, acReverse #-}

instance AbstractContainer Text.Text where
  acLen = Text.length
  acTake = Text.take
  acDrop = Text.drop
  acIndex t i = wrapHi $ Text.singleton $ t `Text.index` i
  acReverse = Text.reverse
  acFold f = Text.foldl' (\acc c -> f acc (wrapHi $ Text.singleton c))

instance (a ~ HiValue) => AbstractContainer (Seq a) where
  acLen = Seq.length
  acTake = Seq.take
  acDrop = Seq.drop
  acIndex = Seq.index
  acReverse = Seq.reverse
  acFold = foldl'

instance AbstractContainer ByteString where
  acLen = ByteString.length
  acTake = ByteString.take
  acDrop = ByteString.drop
  acIndex b i = HiValueNumber $ fromIntegral $ b `ByteString.index` i
  acReverse = ByteString.reverse
  acFold f = ByteString.foldl' (\acc c -> f acc (HiValueNumber $ fromIntegral c))

-- | type erased container
data ErasedContainer = forall a. (AbstractContainer a) => ErasedContainer a

instance HiValueWrap ErasedContainer where
  wrapHi (ErasedContainer a) = wrapHi a

-- is it possible to automatically implement it? (without TH)
instance AbstractContainer ErasedContainer where
  acLen (ErasedContainer a) = acLen a
  acTake i (ErasedContainer c) = ErasedContainer $ acTake i c
  acDrop i (ErasedContainer c) = ErasedContainer $ acDrop i c
  acIndex (ErasedContainer a) i = acIndex a i
  acReverse (ErasedContainer a) = ErasedContainer $ acReverse a
  acFold f s (ErasedContainer a) = acFold f s a

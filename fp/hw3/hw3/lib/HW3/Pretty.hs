module HW3.Pretty (prettyValue) where

import Data.ByteString (ByteString)
import qualified Data.ByteString as ByteString
import Data.Char (chr, ord, toLower)
import Data.Foldable
import qualified Data.List as List
import qualified Data.Map as Map
import Data.Scientific
import Data.Word (Word8)
import GHC.Real (Ratio (..))
import Prettyprinter
import Prettyprinter.Render.Terminal

import HW3.Base
import HW3.FunctionStrings

-- | map from function to its name
funPretty :: Map.Map HiFun (Doc AnsiStyle)
funPretty = Map.fromList $ map (\(s, f) -> (f, pretty s)) allFunctions

hex :: Int -> Char
hex c
  | c >= 0 && c <= 9 = chr $ o0 + c
  | c >= 10 && c <= 15 = chr $ a + c - 10
  | otherwise = undefined
  where
    a = ord 'a'
    o0 = ord '0'

byte2Hex :: Word8 -> Doc AnsiStyle
byte2Hex w = pretty [hex h, hex l]
  where
    (h, l) = fromIntegral w `divMod` 16

prettyStr :: Show s => s -> Doc AnsiStyle
prettyStr = annotate (color Magenta) . pretty . show

prettyBytes :: ByteString -> Doc AnsiStyle
prettyBytes b =
  let children = map byte2Hex (ByteString.unpack b) in
  annotate (color Yellow) $ encloseSep (pretty "[# ") (pretty " #]") (pretty " ") children

prettyValue :: HiValue -> Doc AnsiStyle
prettyValue (HiValueNumber rat@(n :% d))
  | d == 1 = pretty $ show n
  | mod25 d = pretty $ formatScientific Fixed Nothing $ fromRational rat
  | otherwise =
    let
      (q, r) = quotRem n d
      pref =
        case q `compare` 0 of
          EQ -> show r
          LT -> show q ++ " - " ++ show (abs r)
          GT -> show q ++ " + " ++ show r
  in pretty $ pref ++ "/" ++ show d
  where
    mod25 d
      | d <= 1 = True
      | even d = mod25 (d `div` 2)
      | d `mod` 5 == 0 = mod25 (d `div` 5)
      | otherwise = False
prettyValue (HiValueBool b) = annotate (color Yellow) $ pretty $ map toLower $ show b
prettyValue (HiValueFunction f) = annotate (bold <> color Cyan) (funPretty Map.! f)
prettyValue HiValueNull = annotate (underlined <> color Yellow) $ pretty "null"
prettyValue (HiValueString s) = prettyStr s
prettyValue (HiValueList l) =
  let children = map prettyValue (toList l) in
  encloseSep (pretty "[ ") (pretty " ]") (pretty ", ") children
prettyValue (HiValueBytes b) = prettyBytes b
prettyValue (HiValueAction act) =
  case act of
    HiActionCwd       -> pretty "cwd"
    HiActionRead r    -> inf "read" [prettyStr r]
    HiActionWrite r s -> inf "write"[prettyStr r, prettyBytes s]
    HiActionMkDir r   -> inf "mkdir" [prettyStr r]
    HiActionChDir d   -> inf "cd" [prettyStr d]
    HiActionNow       -> inf "now" []
    HiActionRand a b  -> inf "rand" [prettyStr a, pretty b]
    HiActionEcho a    -> inf "echo" [prettyStr a]
  where
    inf :: String -> [Doc AnsiStyle] -> Doc AnsiStyle
    inf name suf =
      let controlForm = annotate (color Blue) . pretty in
      annotate (color Red) (pretty name) <>
      if null suf
      then mempty
      else
        controlForm "("
        <> fold (List.intercalate [controlForm ", "] (map listSingleton suf))
        <> controlForm ")"
prettyValue (HiValueTime b) = pretty "parse-time(" <> prettyStr (show b) <> pretty ")"
prettyValue (HiValueDict d) =
  let
    children =
      map
        (\(k, v) -> prettyValue k <> pretty ": " <> prettyValue v)
        (Map.toList d) in
  encloseSep (pretty "{ ") (pretty " }") (pretty ", ") children

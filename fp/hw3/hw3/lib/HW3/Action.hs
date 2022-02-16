{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module HW3.Action
  ( HiPermission (..)
  , PermissionException (..)
  , HIO (..)
  ) where

import Control.Exception
import Control.Monad.Extra
import Control.Monad.Reader
import qualified Data.ByteString as BS
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Text.Encoding as TextEnc
import qualified Data.Text.IO as TextIO
import Data.Time.Clock (getCurrentTime)
import qualified System.Directory as Dir
import System.Random (randomRIO)

import HW3.AbstractContainer
import HW3.Base

data HiPermission
  = AllowRead
  | AllowWrite
  | AllowTime
  deriving (Show, Eq, Ord, Enum, Bounded)

-- | exception in case permission not satisfied
-- (why not just return null?)
newtype PermissionException
  = PermissionRequired HiPermission
  deriving (Show)

instance Exception PermissionException

-- | instance that redirects actions to actual IO (with permission checking)
-- why are we disallowed to use ReaderT IO?
newtype HIO a
  = HIO { runHIO :: Set HiPermission -> IO a }
  deriving
    ( Functor
    , Applicative
    , Monad
    , MonadReader (Set HiPermission)
    , MonadIO
    )
    via (ReaderT (Set HiPermission) IO)

ensurePermission :: HiPermission -> HIO ()
ensurePermission s =
  unlessM (reader $ Set.member s) $ throw (PermissionRequired s)

catchHIO :: Exception e => HIO a -> (e -> HIO a) -> HIO a
catchHIO HIO { runHIO = t } c =
  HIO $ \s -> t s `catch` \e -> runHIO (c e) s

instance HiMonad HIO where
  runAction act = case act of
    HiActionRead p -> do
      ensurePermission AllowRead
      -- isDir <- liftIO $ Dir.doesDirectoryExist p
      (do
        s <- liftIO $ Dir.listDirectory p
        return $ wrapHi $ wrapHi . Text.pack <$> s)
        `catchHIO` (\(_ :: IOException) -> do
          s <- liftIO $ BS.readFile p
          return $ either (const $ wrapHi s) wrapHi $ TextEnc.decodeUtf8' s)
        `catchHIO` \(_ :: IOException) -> return HiValueNull
    HiActionWrite p b -> do
      ensurePermission AllowWrite
      liftIO $ BS.writeFile p b
      return HiValueNull
    HiActionMkDir p -> do
      ensurePermission AllowWrite
      liftIO $ Dir.createDirectory p
      return HiValueNull
    HiActionChDir p -> do
      ensurePermission AllowRead -- why read?!
      liftIO $ Dir.setCurrentDirectory p
      return HiValueNull
    HiActionCwd -> do
      ensurePermission AllowRead
      wrapHi . Text.pack <$> liftIO Dir.getCurrentDirectory
    HiActionNow -> do
      ensurePermission AllowTime
      wrapHi <$> liftIO getCurrentTime
    HiActionRand l u -> do
      wrapHi <$> randomRIO (l, u)
    HiActionEcho t -> do
      ensurePermission AllowWrite
      liftIO $ TextIO.putStrLn t
      return HiValueNull

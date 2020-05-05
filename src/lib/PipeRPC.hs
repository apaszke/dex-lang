-- Copyright 2019 Google LLC
--
-- Use of this source code is governed by a BSD-style
-- license that can be found in the LICENSE file or at
-- https://developers.google.com/open-source/licenses/bsd

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}

module PipeRPC (PipeServer, startPipeServer, callPipeServer) where

import Control.Concurrent.MVar
import Control.Monad
import Control.Monad.IO.Class
import Data.Aeson
import Data.ByteString.Lazy.Char8 (pack, unpack)
import GHC.IO.Handle.FD
import System.IO
import System.Process

data PipeServer (methods :: [*])
 = PipeServer { _psLock          :: MVar ()
              , _psSendHandle    :: Handle
              , _psReceiveHandle :: Handle }

startPipeServer :: MonadIO m => FilePath -> [String] -> m (PipeServer methods)
startPipeServer cmd args = liftIO $ do
  ((clientRead, _), (_, serverWrite)) <- createPipeWithNames
  ((_, serverRead), (clientWrite, _)) <- createPipeWithNames
  void $ createProcess $ proc cmd $ args ++ [serverRead, serverWrite]
  lock <- newMVar ()
  return $ PipeServer lock clientWrite clientRead

class Member elem (list :: [*]) where
  index :: Int

instance {-# OVERLAPPING #-} Member h (h ': t) where
  index = 0

instance {-# OVERLAPPABLE #-} Member e t => Member e (h ': t) where
  index = 1 + index @e @t

callPipeServer :: forall a b methods m
               .  (MonadIO m, ToJSON a, FromJSON b, Member (a -> b) methods)
               => PipeServer methods -> a -> m b
callPipeServer (PipeServer lock sendHandle receiveHandle) arg = liftIO $ do
  void $ takeMVar lock
  let request = unpack $ encode (index @(a -> b) @methods, arg)
  hPutStrLn sendHandle request
  response <- hGetLine receiveHandle
  putMVar lock ()
  case eitherDecode (pack response) of
    Right x -> case x of
      Right x' -> return x'
      Left s -> error $ "Error thrown by server:\n" ++ s
    Left s -> error $ s ++ "\nDecoding error. Full response:\n" ++ response

createPipeWithNames :: IO ((Handle, String), (Handle, String))
createPipeWithNames = do
  (r, w) <- createPipe
  hSetBuffering r LineBuffering
  hSetBuffering w LineBuffering
  rName <- unixHandleName r
  wName <- unixHandleName w
  return ((r,rName), (w, wName))

unixHandleName :: Handle -> IO String
unixHandleName h = do
  fd <- handleToFd h
  return $ "/dev/fd/" ++ show fd

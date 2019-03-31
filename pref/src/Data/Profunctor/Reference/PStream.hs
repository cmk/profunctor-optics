{-# LANGUAGE TemplateHaskell, CPP #-}

module Data.Profunctor.Reference.PStream where

import Data.Profunctor.Optic
import Data.Profunctor.Reference.Types
import Data.Profunctor.Reference.Global

import Control.Monad.IO.Unlift
import System.IO.Streams (InputStream, OutputStream)
import qualified System.IO.Streams as S
import qualified System.IO.Streams.Combinators as SC


type PStream c b a = P OutputStream InputStream c b a

type InputPStream c a = P' InputStream c a

type OutputPStream c b = P' OutputStream c b


-- | Read a value from a 'PStream' with profunctorial choice.
previewPStream 
  :: MonadIO m 
  => c (Previewed a)
  => PStream c b a 
  -> m (Maybe a)
previewPStream (P o _ rs) = 
  (liftIO $ S.read rs) >>= return . (>>= (\s -> preview o s))


{-
-- | A variant of 'previewPStream' that closes the output stream when
--
-- the input stream is no longer producing values.
matchPStream
  :: c (Matched a)
  => PStream c b a 
  -> IO (Maybe a)
matchPStream (P o rt rs) =


  do s <- readIORef rs
     case match o s of
       Left t -> 
         writeIORef rt t >> return Nothing
       Right a ->
         return $ Just a


connect :: InputStream a -> OutputStream a -> IO () Source#
connectPStream (P o rt rs) = 


read :: MonadUnliftIO m => InputStream a -> m (Maybe a)
read as = liftIO $ S.read as
map :: MonadUnliftIO m => (a -> b) -> InputStream a -> m (InputStream b)
map f is = liftIO $ SC.map f is

modifyPRef 
  :: c (->)
  => PRef IORef c b a 
  -> (a -> b) 
  -> IO ()
modifyPRef (P o rt rs) f = readIORef rs >>= writeIORef rt . over o f

-}


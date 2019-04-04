{-# LANGUAGE TemplateHaskell, CPPRef #-}

module Data.Profunctor.Reference.PStream where

import Data.Profunctor.Optic
import Data.Profunctor.Reference.Types
import Data.Profunctor.Reference.Global

import Control.Monad.IO.Unlift
import System.IO.Streams (InputStream, OutputStream)
import qualified System.IO.Streams as S
import qualified System.IO.Streams.Combinators as SC


---------------------------------------------------------------------
--  Connecting 'PStream's
---------------------------------------------------------------------

-- | Connect the underlying 'InputStream' and 'OutputStream'. 
--
-- Propagates the end-of-stream message from the 'InputStream' 
-- through to the 'OutputStream'. The connection ends when the 
-- 'InputStream' yields a 'Nothing'.

{-# INLINE connectPStream #-}

connectPStream
  :: MonadIO m 
  => c (->)
  => PStream c b a
  -> (a -> b)
  -> m ()
connectPStream (PRef o rs rt) f = liftIO $ loop
  where loop = do
          ms <- S.read rs
          maybe (S.write Nothing rt)
                (\t -> S.write (Just $ over o f t) rt >> loop)
                ms


-- | Prismatic variant of 'connectPStream'.
--
-- Supply a default value of 'a' for inputs that fail to match the
-- underlying prism.

connectPStream'
  :: MonadIO m 
  => c (Costar Maybe)
  => PStream c b a
  -> a
  -> (a -> b)
  -> m ()
connectPStream' (PRef o rs rt) a f = liftIO $ loop
  where loop = do
          ms <- S.read rs
          S.write (Just $ pmaybe o a f ms) rt >> loop




-- | Connects an 'InputStream' to an 'OutputStream' without passing the
-- end-of-stream notification through to the 'OutputStream'.
--
-- Use this to supply an 'OutputStream' with multiple 'InputStream's and use
-- 'connect' for the final 'InputStream' to finalize the 'OutputStream', like
-- so:
--
-- @
-- do Streams.'supply'  input1 output
--    Streams.'supply'  input2 output
--    Streams.'connect' input3 output
-- @

{-# INLINE supplyPStream #-}
-- TODO: update description to cover PStream composition
supplyPStream
  :: MonadIO m 
  => c (->)
  => PStream c b a
  -> (a -> b)
  -> m ()
supplyPStream (PRef o rs rt) f = liftIO $ loop
  where loop = do
          ms <- S.read rs
          maybe (return $! ())
                (\s -> S.write (Just $ over o f s) rt >> loop)
                ms


---------------------------------------------------------------------
--  Reading 'PStream's
---------------------------------------------------------------------


-- | Read a value from a 'PStream' with profunctorial choice.
--
-- This function consumes input stream values regardless of whether
-- they match the underlying prism.
--
--  A return value of @'Nothing'@ indicates that either the underlying
-- 'InputStream' was empty, or that it was full and that the @a@ was not 
-- present.

previewPStream 
  :: MonadIO m 
  => c (Previewed a)
  => PStream c b a 
  -> m (Maybe a)
previewPStream (PRef o rs _) =
  liftIO (S.read rs) >>= readPrism o


-- | A variant of 'previewPStream' that only consumes the stream element 
--  if the underlying prism matches. Handy if there are multiple consumers.
-- 
--  A return value of @'Nothing'@ indicates that either the underlying
-- 'InputStream' was empty, or that it was full and that the @a@ was not 
-- present.

previewPStream'
  :: MonadIO m 
  => c (Previewed a)
  => PStream c b a 
  -> m (Maybe a)
previewPStream' (PRef o rs _) = 
  do ma <- liftIO (S.peek rs) >>= readPrism o 
     case ma of
       Nothing -> 
         return Nothing
       Just _ -> 
         liftIO (S.read rs) >>= readPrism o


-- | A variant of 'previewPStream' that writes the error value 't' to
-- 
-- the output stream whenever an 'a' is not available.

matchPStream
  :: MonadIO m 
  => c (Matched a)
  => PStream c b a 
  -> m (Maybe a)
matchPStream (PRef o rs rt) = 
  do meta <- liftIO (S.read rs) 
     case meta of
       Nothing ->
         return Nothing
       Just eta ->
         either (\t -> liftIO $ S.write (Just t) rt >> return Nothing)
                (return . Just)
                (match o eta)
         

-- | A variant of 'matchPStream' that additionally closes the output
-- 
-- stream once the input stream is no longer producing values.

matchPStream'
  :: MonadIO m 
  => c (Matched a)
  => PStream c b a 
  -> m (Maybe a)
matchPStream' (PRef o rs rt) = error "TODO"


readPrism 
  :: Monad m 
  => Optic (Previewed a) s t a b 
  -> Maybe s 
  -> m (Maybe a)
readPrism o = return . (>>= preview o)




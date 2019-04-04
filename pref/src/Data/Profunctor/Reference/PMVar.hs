{-# LANGUAGE AllowAmbiguousTypes, TypeApplications, ScopedTypeVariables, FlexibleInstances #-}

module Data.Profunctor.Reference.PMVar
  ( PMVar
  , newEmptyPMVar
  , newPMVar
  , takePMVar
  , putPMVar
  , readPMVar
  , tryReadPMVar
  , previewPMVar
  , tryPreviewPMVar
  , swapPMVar
  , tryTakePMVar
  , tryPutPMVar
  , isEmptyPMVar
  , withPMVar
  , withPMVarMasked
  , modifyPMVar
  , modifyPMVar_
  , modifyPMVarMasked
  , modifyPMVarMasked_
  ) where

import Data.Profunctor.Optic
import Data.Profunctor.Reference.Types
import Data.Profunctor.Reference.Global

import System.Mem.Weak (Weak)
import Control.Arrow
import Control.Concurrent.MVar (MVar)
import Control.Monad.IO.Unlift
import qualified Control.Concurrent.MVar as M


---------------------------------------------------------------------
--  Creating 'PMVar's
---------------------------------------------------------------------


-- | Create a new 'PMVar'.

{-# INLINE newPMVar #-}

newPMVar :: MonadIO m => Optical' c s a -> s -> m (PMVar c a)
newPMVar o s = liftIO $ (PRef' o) <$> M.newMVar s


-- | Create a new empty 'PMVar'. 

{-# INLINE newEmptyPMVar #-}

newEmptyPMVar 
  :: forall m c s a. MonadIO m
  => Optical' c s a
  -> m (PMVar c a)
newEmptyPMVar o = liftIO $ (PRef' o) <$> M.newEmptyMVar @s


---------------------------------------------------------------------
--  Reading 'PMVar's
---------------------------------------------------------------------


-- | Check whether a 'PMVar' is currently empty.

isEmptyPMVar :: MonadIO m => PMVar c a -> m Bool
isEmptyPMVar (PRef' _ rs) = liftIO $ M.isEmptyMVar rs


-- | Return the contents of the 'PMVar'.
--
-- If the 'MVar' is currently empty, 'takeMVar' will wait until it is 
-- full.  After a 'takePMVar', the read-only 'MVar' is left empty.

takePMVar :: MonadIO m => c (Forget a) => PMVar c a -> m a
takePMVar (PRef' o rs) = liftIO $ view o <$> M.takeMVar rs


-- | A non-blocking version of 'takePMVar'.  
--
-- The 'tryTakePMVar' function returns immediately, with 'Nothing' if 
-- the underlying 'MVar' was empty, or @'Just' a@ if it was full with 
-- contents @s@.  After 'tryTakeMVar', the 'MVar' is left empty.

tryTakePMVar :: MonadIO m => c (Forget a) => PMVar c a -> m (Maybe a)
tryTakePMVar (PRef' o rs) = liftIO $ fmap (view o) <$> M.tryTakeMVar rs


-- | Atomically read the contents of a lens-like 'PMVar'.  
--
-- If the underlying 'MVar' is currently empty, 'readPMVar' will wait 
-- until it is full. 'readPMVar' is guaranteed to receive the next 
-- 'putPMVar'.

readPMVar 
  :: MonadIO m 
  => c (Forget a)
  => PMVar c a 
  -> m a
readPMVar (PRef' o rs) = liftIO $ view o <$> M.readMVar rs


-- | Atomically preview the contents of a prism-like 'PMVar'.  
--
-- If the underlying 'MVar' is currently empty, 'readPMVar' will wait 
-- until it is full. 'readPMVar' is guaranteed to receive the next 
-- 'putPMVar'. A return value of @'Nothing'@ is therefore a guarantee 
-- that the @a@ was not present.

previewPMVar
  :: MonadIO m 
  => c (Previewed a)
  => PMVar c a 
  -> m (Maybe a)
previewPMVar (PRef' o rs) = liftIO $ preview o <$> M.readMVar rs


-- | A non-blocking variant of 'readPMVar'.

tryReadPMVar
  :: MonadIO m 
  => c (Forget a)
  => PMVar c a 
  -> m (Maybe a)
tryReadPMVar (PRef' o rs) = liftIO $ fmap (view o) <$> M.tryReadMVar rs


-- | A non-blocking variant of 'previewPMVar'.
-- 
-- A return value of @'Nothing'@ indicates that either the underlying
-- 'MVar' was empty, or that it was full and that the @a@ was not 
-- present.

tryPreviewPMVar
  :: MonadIO m 
  => c (Previewed a)
  => PMVar c a 
  -> m (Maybe a)
tryPreviewPMVar (PRef' o rs) = liftIO $ (>>= preview o) <$> M.tryReadMVar rs



-- | Exception-safe wrapper for operating on the contents of a 'PMVar'.  
--
-- This operation is exception-safe: it will replace the original
-- contents of the underlying 'MVar' 'ms' if an exception is raised.
--
-- However, it is only atomic if there are no other producers for 'ms'.

{-# INLINE withPMVar #-}

withPMVar 
  :: MonadUnliftIO m 
  => c (Forget a)
  => PMVar c a 
  -> (a -> m r) 
  -> m r
withPMVar (PRef' o rs) f = 
     withRunInIO $ \run -> M.withMVar rs (run . f . view o)



-- | Masked variant of 'withPMVar'.

{-# INLINE withPMVarMasked #-}

withPMVarMasked 
  :: MonadUnliftIO m 
  => c (Forget a)
  => PMVar c a 
  -> (a -> m r) 
  -> m r
withPMVarMasked (PRef' o rs) f = 
     withRunInIO $ \run -> M.withMVarMasked rs (run . f . view o)


---------------------------------------------------------------------
--  Modifying 'PMVar's
---------------------------------------------------------------------

-- | Put a value into a 'PMVar'.  
--
-- If the 'PMVar' is currently full, 'putPMVar' will wait until it 
-- becomes empty.

putPMVar
  :: MonadIO m 
  => c Tagged
  => PMVar c a 
  -> a 
  -> m ()
putPMVar (PRef' o rs) a = liftIO $ M.putMVar rs . review o $ a


-- | A non-blocking version of 'putPMVar'.  
--
-- The 'tryPutMVar' function attempts to put the value @a@ into the 
-- underlying 'MVar', returning 'True' if it was successful, or 
-- 'False' otherwise.

tryPutPMVar
  :: MonadIO m 
  => c Tagged
  => PMVar c a 
  -> a 
  -> m Bool
tryPutPMVar (PRef' o rs) a = liftIO $ M.tryPutMVar rs . review o $ a


-- |  Take a value from an 'MVar', putting a new value into its place.
--
-- This function is atomic only if there are no other producers for 
-- this 'MVar'. Requires an 'Iso'-like optic.

swapPMVar 
  :: MonadIO m
  => c (Forget a) 
  => c Tagged
  => PMVar c a 
  -> a 
  -> m a
swapPMVar (PRef' o rs) a = liftIO $ 
     view o <$> (M.swapMVar rs . review o $ a)


-- | An exception-safe wrapper for modifying the contents of a 'PMVar'.
--
-- Like 'withPMVar', 'modifyPMVar_' will replace the original contents
-- of the underlying 'MVar' 'ms' if an exception is raised.
--
-- However, it is only atomic if there are no other producers for 'ms'.

{-# INLINE modifyPMVar_ #-}

modifyPMVar_ 
  :: MonadUnliftIO m
  => c (Star m)
  => PMVar c a
  -> (a -> m a) 
  -> m ()
modifyPMVar_ (PRef' o rs) f = 
     withRunInIO $ \run -> M.modifyMVar_ rs (run . traverseOf o f)


-- | A variant of 'modifyPMVar_' that allows a value to be returned. 

{-# INLINE modifyPMVar #-}

modifyPMVar
  :: MonadUnliftIO m 
  => c (Forget a)
  => c (Star m)
  => PMVar c a
  -> (a -> m (a, r)) 
  -> m r
modifyPMVar (PRef' o rs) f =
 let l = (fmap . fmap) fst f
     l' = traverseOf o l
     r = (fmap . fmap) snd f
     r' = r . view o
     out = (Kleisli l') &&& (Kleisli r')

  in withRunInIO $ \run -> M.modifyMVar rs (run . runKleisli out)


-- | A masked variant of 'modifyPMVar_'. 

{-# INLINE modifyPMVarMasked_ #-}

modifyPMVarMasked_ 
  :: MonadUnliftIO m
  => c (Star m)
  => PMVar c a
  -> (a -> m a) 
  -> m ()
modifyPMVarMasked_ (PRef' o rs) f = 
     withRunInIO $ \run -> M.modifyMVarMasked_ rs (run . traverseOf o f)


-- | A masked variant of 'modifyPMVar'. 

{-# INLINE modifyPMVarMasked #-}

modifyPMVarMasked
  :: MonadUnliftIO m 
  => c (Forget a)
  => c (Star m)
  => PMVar c a
  -> (a -> m (a, r)) 
  -> m r
modifyPMVarMasked (PRef' o rs) f =
 let l = (fmap . fmap) fst f

     l' = traverseOf o l

     r = (fmap . fmap) snd f

     r' = r . view o

     out = (Kleisli l') &&& (Kleisli r')

  in withRunInIO $ \run -> M.modifyMVarMasked rs (run . runKleisli out)

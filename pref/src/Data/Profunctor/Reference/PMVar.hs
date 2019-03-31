{-# LANGUAGE AllowAmbiguousTypes, TypeApplications, ScopedTypeVariables, FlexibleInstances #-}

module Data.Profunctor.Reference.PMVar
  ( --newEmptyPMVar
    newPMVar
  --, takePMVar
  --, putPMVar
  --, readPMVar
  --, swapPMVar
  --, tryTakePMVar
  --, tryPutPMVar
  --, isEmptyPMVar
  --, withPMVar
  --, withPMVarMasked
  --, modifyPMVar
  --, modifyPMVar_
  --, modifyPMVarMasked
  --, modifyPMVarMasked_
  --, tryReadPMVar
  --, mkWeakPMVar
  ) where

import Data.Profunctor.Optic
import Data.Profunctor.Reference.Types
import Data.Profunctor.Reference.Global

import System.Mem.Weak (Weak)
--import System.IO.Unsafe
import Control.Arrow
import Control.Concurrent.MVar (MVar)
import Control.Monad.IO.Unlift
import qualified Control.Concurrent.MVar as M


--type PMVar c b a = P MVar MVar c b a
type PMVar c a = P' MVar c a

---------------------------------------------------------------------
--  Creating 'PMVar's
---------------------------------------------------------------------


-- | Create a new empty 'PMVar'. 
newEmptyPMVar 
  :: forall m c s a. MonadIO m
  => Optical' c s a
  -> m (PMVar c a)
newEmptyPMVar o = liftIO $ (P' o) <$> M.newEmptyMVar @s


-- | Create a new 'PMVar'.
newPMVar :: MonadIO m => Optical' c s a -> s -> m (PMVar c a)
newPMVar o s = liftIO $ (P' o) <$> M.newMVar s


---------------------------------------------------------------------
--  Reading 'PMVar's
---------------------------------------------------------------------


-- | Lifted 'M.isEmptyMVar'.
--
-- @since 0.1.0.0
isEmptyPMVar :: MonadIO m => MVar a -> m Bool
isEmptyPMVar = liftIO . M.isEmptyMVar

-- | Return the contents of the 'PMVar'.
--
-- If the 'MVar' is currently empty, 'takeMVar' will wait until it is 
-- full.  After a 'takePMVar', the read-only 'MVar' is left empty.
--
{-# INLINE takePMVar #-}
takePMVar :: MonadIO m => c (Forget a) => PMVar c a -> m a
takePMVar (P' o ms) = liftIO $ view o <$> M.takeMVar ms

tryTakePMVar :: MonadIO m => MVar a -> m (Maybe a)
tryTakePMVar = liftIO . M.tryTakeMVar

readPMVar :: MonadIO m => MVar a -> m a
readPMVar = liftIO . M.readMVar

-- | Lifted 'M.tryReadMVar'.
--
-- @since 0.1.0.0
tryReadPMVar :: MonadIO m => MVar a -> m (Maybe a)
tryReadPMVar = liftIO . M.tryReadMVar


-- | Exception-safe wrapper for operating on the contents of a 'PMVar'.  
--
-- This operation is exception-safe: it will replace the original
-- contents of the underlying 'MVar' 'ms' if an exception is raised.
--
-- However, it is only atomic if there are no other producers for 'ms'.
--
{-# INLINE withPMVar #-}
withPMVar 
  :: MonadUnliftIO m 
  => c (Forget a)
  => PMVar c a 
  -> (a -> m r) 
  -> m r
withPMVar (P' o ms) f = 
  withRunInIO $ \run -> M.withMVar ms (run . f . view o)


-- | Masked variant of 'withPMVar'.
--
{-# INLINE withPMVarMasked #-}
withPMVarMasked 
  :: MonadUnliftIO m 
  => c (Forget a)
  => PMVar c a 
  -> (a -> m r) 
  -> m r
withPMVarMasked (P' o ms) f = 
     withRunInIO $ \run -> M.withMVarMasked ms (run . f . view o)


---------------------------------------------------------------------
--  Modifying 'PMVar's
---------------------------------------------------------------------

{-


-- | Lifted 'M.swapMVar'.
--
-- @since 0.1.0.0
swapPMVar :: MonadIO m => PMVar a -> a -> m a
swapPMVar var = liftIO . M.swapMVar var

-- | Lifted 'M.putMVar'.
--
-- @since 0.1.0.0
putPMVar :: MonadIO m => PMVar a -> a -> m ()
putPMVar var = liftIO . M.putMVar var

-- | Lifted 'M.tryPutMVar'.
--
-- @since 0.1.0.0
tryPutPMVar :: MonadIO m => PMVar a -> a -> m Bool
tryPutPMVar var = liftIO . M.tryPutMVar var


-}

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
modifyPMVar_ (P' o ms) f = 
     withRunInIO $ \run -> M.modifyMVar_ ms (run . traverseOf o f)


-- | A variant of 'modifyPMVar_' that allows a value to be returned. 
--
{-# INLINE modifyPMVar #-}
modifyPMVar
  :: MonadUnliftIO m 
  => c (Forget a)
  => c (Star m)
  => PMVar c a
  -> (a -> m (a, r)) 
  -> m r
modifyPMVar (P' o ms) f =
 let l = (fmap . fmap) fst f

     l' = traverseOf o l

     r = (fmap . fmap) snd f

     r' = r . view o

     out = (Kleisli l') &&& (Kleisli r')

  in withRunInIO $ \run -> M.modifyMVar ms (run . runKleisli out)


-- | A masked variant of 'modifyPMVar_'. 
--
{-# INLINE modifyPMVarMasked_ #-}
modifyPMVarMasked_ 
  :: MonadUnliftIO m
  => c (Star m)
  => PMVar c a
  -> (a -> m a) 
  -> m ()
modifyPMVarMasked_ (P' o ms) f = 
     withRunInIO $ \run -> M.modifyMVarMasked_ ms (run . traverseOf o f)


-- | A masked variant of 'modifyPMVar'. 
--
{-# INLINE modifyPMVarMasked #-}
modifyPMVarMasked
  :: MonadUnliftIO m 
  => c (Forget a)
  => c (Star m)
  => PMVar c a
  -> (a -> m (a, r)) 
  -> m r
modifyPMVarMasked (P' o ms) f =
 let l = (fmap . fmap) fst f

     l' = traverseOf o l

     r = (fmap . fmap) snd f

     r' = r . view o

     out = (Kleisli l') &&& (Kleisli r')

  in withRunInIO $ \run -> M.modifyMVarMasked ms (run . runKleisli out)



{-# LANGUAGE BangPatterns, MultiParamTypeClasses #-}

module Data.Ref where

import Control.Concurrent.MVar
import Control.Concurrent.STM
import Control.Monad.ST
import Data.IORef
import Data.STRef

import Data.Function (($), (&))
import Data.Functor (($>))

-------------------------------------------------------------------------------
-- Ref
-------------------------------------------------------------------------------

{- |

A typeclass for mutable rerences.

Type variables:

* @r@ - The rerence (e.g. 'IORef', 'TVar', 'MVar', 'TMVar')

* @m@ - The monad in which the modification takes place (e.g. 'IO', 'STM')

-}


class Monad m => Ref m r where
    -- | Create a new rerence.
    newRef :: a -- ^ An initial value
           -> m (r a)
    -- | Reads a rerence.
    readRef :: r a -- ^ Reference
            -> m a
    -- | Write to rerence.
    writeRef :: r a -- ^ Reference
             -> a -- ^ New value
             -> m ()

--------------------------------------------------------------------------------
--  Functions
--------------------------------------------------------------------------------


-- Be warned that 'modifyRef' does not apply the function strictly.  This
-- means if the program calls 'modifyRef' many times, but seldomly uses the
-- value, thunks will pile up in memory resulting in a space leak. 
--
-- To avoid this problem, use 'modifyRef'' instead.
modifyRef :: Ref m r => r a -> (a -> a) -> m ()
modifyRef r f = readRef r >>= writeRef r . f

-- | Strict version of 'modifyRef'
modifyRef' :: Ref m r => r a -> (a -> a) -> m ()
modifyRef' r f = do
    x <- readRef r
    let x' = f x
    x' `seq` writeRef r x'

--------------------------------------------------------------------------------
--  Instances
--------------------------------------------------------------------------------


instance Ref IO IORef where
    newRef = newIORef
    readRef = readIORef
    writeRef = writeIORef

instance Ref (ST s) (STRef s) where
    newRef = newSTRef
    readRef = readSTRef
    writeRef = writeSTRef

instance Ref IO MVar where
    newRef = newMVar
    readRef = readMVar
    writeRef = putMVar

instance Ref STM TVar where
    newRef = newTVar
    readRef = readTVar
    writeRef = writeTVar

instance Ref STM TMVar where
    newRef = newTMVar
    readRef = takeTMVar
    writeRef = putTMVar

instance Ref IO TVar where
    newRef = newTVarIO
    readRef r = atomically $ readRef r
    writeRef r a = atomically $ writeRef r a

instance Ref IO TMVar where
    newRef = newTMVarIO
    readRef r = atomically $ readRef r
    writeRef r a = atomically $ writeRef r a


--------------------------------------------------------------------------------
--  MRef
--------------------------------------------------------------------------------

{- |

A typeclass for mutex-based rerences that have blocking take/put operations.

Type variables:

* @r@ - The rerence (e.g. 'IORef', 'TVar', 'MVar', 'TMVar')
* @m@ - The monad in which the modification takes place (e.g. 'IO', 'STM')
-}
class Ref m r => MRef m r where

    newEmptyRef :: m (r a)

    {- |
    Return the contents of a mutex reference. If the refence is currently empty, 
    the transaction will retry. 

    After a 'takeRef', the refence is left empty.
    -}
    takeRef :: r a -> m a

    tryTakeRef :: r a -> m (Maybe a)

    putRef :: r a -> a -> m ()

    tryPutRef :: r a -> a -> m Bool

    swapRef :: r a -> a -> m a

    isEmptyRef :: r a -> m Bool


instance MRef IO MVar where

    newEmptyRef = newEmptyMVar

    takeRef = takeMVar

    tryTakeRef = tryTakeMVar

    putRef = putMVar

    tryPutRef = tryPutMVar

    swapRef = swapMVar

    isEmptyRef = isEmptyMVar


instance MRef STM TMVar where

    newEmptyRef = newEmptyTMVar

    takeRef = takeTMVar

    tryTakeRef = tryTakeTMVar

    putRef = putTMVar

    tryPutRef = tryPutTMVar

    swapRef = swapTMVar

    isEmptyRef = isEmptyTMVar


instance MRef IO TMVar where

    newEmptyRef = newEmptyTMVarIO

    takeRef = atomically . takeRef

    tryTakeRef = atomically . tryTakeRef

    putRef r = atomically . putRef r

    tryPutRef r = atomically . tryPutRef r

    swapRef r = atomically . swapRef r

    isEmptyRef = atomically . isEmptyRef

--------------------------------------------------------------------------------
--  ARef
--------------------------------------------------------------------------------

{- |
A typeclass for mutable rerences that have an atomic modify operation.

Type variables:

* @r@ - The rerence (e.g. 'IORef', 'TVar', 'MVar', 'TMVar')
* @m@ - The monad in which the modification takes place (e.g. 'IO', 'STM')

As the name "atomic" implies, these functions are useful for using mutable
references in a safe way to prevent race conditions in a multithreaded
program.

The implementation is required to ensure that reordering of memory
operations cannot cause type-correct code to go wrong.  In
particular, when inspecting the value read from an 'ARef', the
memory writes that created that value must have occurred from the
point of view of the current thread.
-}

class Ref m r => ARef m r where

  {- |

  Atomically modify the contents of a @ref@ (type @a@) and produce a value (type
  @b@). This is lazy, which means if the program calls 'atomicModifyRef' many
  times, but seldomly uses the value, thunks will pile up in memory resulting in
  a space leak. To update strictly use 'atomicModifyRef''

  -}
  atomicModifyRef :: r a -> (a -> (a, b)) -> m b


--------------------------------------------------------------------------------
--  Functions
--------------------------------------------------------------------------------

-- | Strict variant of 'atomicModifyRef'.  
--
-- This forces both the value stored as well as the value returned.
atomicModifyRef' :: ARef m r => r a -> (a -> (a, b)) -> m b
atomicModifyRef' r f = do
    b <- atomicModifyRef r $ \a ->
            case f a of
                v@(a',_) -> a' `seq` v
    b `seq` return b


-- | Variant of 'writeRef' with the \"barrier to reordering\" property that
--
-- 'atomicModifyRef' has.
atomicWriteRef :: ARef m r => r a -> a -> m ()
atomicWriteRef r a = atomicModifyRef r (\_ -> (a, ()))


-- | Strict variant of 'atomicWriteRef'.
atomicWriteRef' :: ARef m r => r a -> a -> m ()
atomicWriteRef' r a = do
    x <- atomicModifyRef r (\_ -> (a, ()))
    x `seq` return ()


--------------------------------------------------------------------------------
--  Instances
--------------------------------------------------------------------------------

instance ARef IO IORef where
    atomicModifyRef r f = atomicModifyIORef r f

instance ARef IO MVar where
    atomicModifyRef r f = modifyMVar r (\x -> pure $  f x)

instance ARef STM TVar where
    atomicModifyRef r f =
      readTVar r >>= \a -> f a & \( a',  b) -> writeTVar r a' $> b

instance ARef STM TMVar where
    atomicModifyRef r f =
      takeTMVar r >>= \a -> f a & \( a',  b) -> putTMVar r a' $> b

instance ARef IO TVar where
    atomicModifyRef r f = atomically (atomicModifyRef r f)

instance ARef IO TMVar where
    atomicModifyRef r f = atomically (atomicModifyRef r f)

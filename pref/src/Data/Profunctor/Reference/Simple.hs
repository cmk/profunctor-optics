{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE UndecidableInstances      #-}

{-# LANGUAGE TypeApplications        #-}
{-# OPTIONS_GHC -w #-}
{-# LANGUAGE TemplateHaskell, CPP #-}
module Data.Profunctor.Reference.Simple where


import Control.Concurrent.MVar (MVar)
import Control.Concurrent.STM (TArray, TBQueue, TQueue, TChan, TMVar, TVar)
import Control.Monad.Reader (MonadReader(..))
import Control.Monad.State  (MonadState(..))
import Control.Monad.Writer (MonadWriter(..))
import Control.Monad.IO.Unlift
import Data.IORef (IORef(..))
import Data.Profunctor.Optic
import System.IO.Streams (InputStream, OutputStream)

import qualified Data.IORef as IOR

import qualified Control.Monad.Trans.Reader as R
import Data.Profunctor.Reference.Global


---------------------------------------------------------------------
--  PRef'
---------------------------------------------------------------------


{- | A profunctor reference is a pair of mutable references bound 

together with a profunctor optic by existentializing over the types
 
in the read and write references.

The type variables signify:

  * @c@ - The constraint determining which operations can be performed.

  * @rs@ - The read container reference (e.g. 'MVar', 'IO', 'IORef' etc.).

  * @a@ - The exposed type.

-}

data PRef' c rs a = forall x . PRef' (Optical' c x a) !(rs x)

--instance Functor (PRef' Profunctor rs) where fmap f (PRef' o rs) = PRef' (o . dimap id f) rs

-- | Unbox a 'Pxy' by providing an existentially quantified continuation.
withPRef'
  :: PRef' c rs a 
  -> (forall x . Optical' c x a -> rs x -> r) 
  -> r
withPRef' (PRef' o rs) f = f o rs

{-

newtype LocalRef c s a = 
  LocalRef { unLocalRef :: Ref m r => forall r. ReaderT (PRef' STRef c s) (ST r) a }

modifyPRef' :: Ref r m => PRef' r Mapping a -> (a -> a) -> m ()
modifyPRef' (PRef' o rs) f = modifyRef' rs $ over o f

atomicModifyPRef' :: ARef r m => PRef' r Strong a -> (a -> (a, x)) -> m x
atomicModifyPRef' (PRef' o rs) f = atomicModifyRef' rs ssa
    where ssa = withLens o $ \sa sas -> \s -> let (a, x) = f . sa $! s in (sas s a, x)


type PIORef' c a = PRef' c IORef a

type PMVar c b a = PRef c MVar MVar b a

type PTChan c b a = PRef c TChan TChan b a

type PTChan' c a = PRef' c TChan a

type PTQueue c b a = PRef c TQueue TQueue b a

type PTQueue' c a = PRef' c TQueue a

type PTBQueue c b a = PRef c TBQueue TBQueue b a

type PTBQueue' c a = PRef' c TBQueue a

-}

type PIORef c a = PRef' c IORef a

type PMVar c a = PRef' c MVar a

type PInputStream c a = PRef' c InputStream a

type POutputStream c b = PRef' c OutputStream b



readPIORef 
  :: MonadIO m
  => c (Star (Const a))
  => PRef' c IORef a 
  -> m a
readPIORef (PRef' o rs) = liftIO $ view o <$> IOR.readIORef rs

modifyPIORef
  :: MonadIO m
  => c (->)
  => PRef' c IORef a 
  -> (a -> a) 
  -> m ()
modifyPIORef (PRef' o rs) f = liftIO $ IOR.readIORef rs >>= IOR.writeIORef rs . over o f




declareIORef "t" [t| (Int, Int) |] [e| (4, 2) |]

s :: PRef' Strong IORef Int
s = PRef' _1 t

--getInt = get @(PRef' Strong IORef Int)

{-

instance MonadState a (R.ReaderT (PRef' Strong IORef a) IO)  where 

  get = do
    ref <- R.ask
    readPIORef ref

  put a = do
    ref <- R.ask
    liftIO $ modifyPIORef ref (const a)

foo :: R.ReaderT (PRef' Strong IORef Int) IO Int
foo = do
  a <- get @Int
  put (a+1)
  b <- get @Int
  return b

use :: MonadState s m => AGetter a s t a b -> m a
use l = State.gets (view l)


getex :: MonadState s m => c (Star (Const a)) => PRef c rt ((->) s) b a -> m a
getex (PRef o rs _) = view o <$> gets rs

puts :: MonadState s m => (a -> s) -> a -> m ()
puts f = put . f

putex :: MonadState s m => c (Star (Const a)) => PRef c rt ((->) s) b a -> m a
putex p@(PRef o _ rt) = getex p >>= view o <$> gets rs



instance (MonadIO m, MonadReader (PIORef Strong b a) m, Monoid b) => MonadWriter b m where 

  tell b = do
    ref <- ask
    liftIO $ modifyPIORef' ref (const b) --TODO `mappend` 

  pass act = do
    (a, f) <- act
    ref <- ask
    liftIO $ modifyPIORef' ref f
    return a
{-
  listen act = do
    w1 <- ask >>= liftIO . readPIORef
    a <- act
    w2 <- do
      ref <- ask
      v <- liftIO $ readPIORef ref
      _ <- liftIO $ modifyPIORef' ref (const w1)
      return v
    return (a, w2)
-}
-}

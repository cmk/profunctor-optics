{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE QuantifiedConstraints     #-}

{-# OPTIONS_GHC -w #-}
{-# LANGUAGE TemplateHaskell, CPP #-}
module Data.Profunctor.Reference.PRef (
    module Export
  , module Data.Profunctor.Reference.PRef
) where


import Control.Monad.Reader (MonadReader(..), asks)
import Control.Monad.State  (MonadState(..), gets)
import Control.Monad.Writer (MonadWriter(..))
import Control.Monad.IO.Unlift
import Data.StateVar as Export
-- (HasGetter(..), HasSetter(..), HasUpdate(..), ($=), ($=!), ($~), ($~!))
import Data.Profunctor.Optic

import qualified Data.IORef as IOR
import qualified Data.StateVar as SV
import qualified Control.Monad.Trans.Reader as R
import Data.Profunctor.Reference.Global

import Data.IORef (IORef(..))

---------------------------------------------------------------------
--  PRef
---------------------------------------------------------------------


{- | A 'PRef' is a mutable reference bound together with a profunctor 

optic by existentializing over the 's' and 't' variables and setting 

them equal to one another. See also 'Data.Profunctor.Reference.PRefs'.

The type variables signify:

  * @c@ - The constraint determining which operations can be performed.

  * @rs@ - The read container reference (e.g. 'MVar', 'IO', 'IORef' etc.).

  * @a@ - The exposed read / write type.

-}

data PRef c rs b a = forall x . PRef (Optical c x x a b) !(rs x)


dimap' :: (b' -> b) -> (a -> a') -> PRef Profunctor rs b a -> PRef Profunctor rs b' a'
dimap' bs sa (PRef o rs) = PRef (o . dimap sa bs) rs

instance Profunctor (PRef Profunctor rs) where dimap = dimap'

instance (forall s . HasGetter (rs s) s) => HasGetter (PRef Getting rs b a) a where

  get (PRef o rs) = liftIO $ view o <$> SV.get rs
  {-# INLINE get #-}

instance (forall s. HasUpdate (rs s) s s) => HasSetter (PRef Mapping rs b a) b where

  (PRef o rs) $= b = liftIO $ rs $~ over o (const b)
  {-# INLINE ($=) #-}

instance (forall s. HasUpdate (rs s) s s) => HasUpdate (PRef Mapping rs b a) a b where

  (PRef o rs) $~ f  = liftIO $ rs $~ over o f

  (PRef o rs) $~! f = liftIO $ rs $~! over o f


--instance Functor (PRef Profunctor rs) where fmap f (PRef o rs) = PRef (o . dimap id f) rs

-- | Unbox a 'Pxy' by providing an existentially quantified continuation.
withPRef
  :: PRef c rs b a 
  -> (forall x . Optical c x x a b -> rs x -> r) 
  -> r
withPRef (PRef o rs) f = f o rs

{-

newtype LocalRef c s a = 
  LocalRef { unLocalRef :: Ref m r => forall r. ReaderT (PRef STRef c s) (ST r) a }

modifyPRef :: Ref r m => PRef r Mapping a -> (a -> a) -> m ()
modifyPRef (PRef o rs) f = modifyRef' rs $ over o f

atomicModifyPRef :: ARef r m => PRef r Strong a -> (a -> (a, x)) -> m x
atomicModifyPRef (PRef o rs) f = atomicModifyRef' rs ssa
    where ssa = withLens o $ \sa sas -> \s -> let (a, x) = f . sa $! s in (sas s a, x)

-}







readPIORef 
  :: MonadIO m
  => c (Star (Const a))
  => PRef c IORef b a 
  -> m a
readPIORef (PRef o rs) = liftIO $ view o <$> IOR.readIORef rs

modifyPIORef
  :: MonadIO m
  => c (->)
  => PRef c IORef b a 
  -> (a -> b) 
  -> m ()
modifyPIORef (PRef o rs) f = liftIO $ IOR.modifyIORef rs (over o f)




declareIORef "t" [t| (Int, Int) |] [e| (4, 2) |]

s :: PRef Strong IORef Int Int
s = PRef _1 t

--getInt = get @(PRef Strong IORef Int)

{-

instance MonadState a (R.ReaderT (PRef Strong IORef a) IO)  where 

  get = do
    ref <- R.ask
    readPIORef ref

  put a = do
    ref <- R.ask
    liftIO $ modifyPIORef ref (const a)

foo :: R.ReaderT (PRef Strong IORef Int) IO Int
foo = do
  a <- get @Int
  put (a+1)
  b <- get @Int
  return b

use :: MonadState s m => AGetter a s t a b -> m a
use l = State.gets (view l)


getex :: MonadState s m => c (Star (Const a)) => PRefs c rt ((->) s) b a -> m a
getex (PRefs o rs _) = view o <$> gets rs

puts :: MonadState s m => (a -> s) -> a -> m ()
puts f = put . f

putex :: MonadState s m => c (Star (Const a)) => PRefs c rt ((->) s) b a -> m a
putex p@(PRefs o _ rt) = getex p >>= view o <$> gets rs
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


censoring
  :: MonadWriter s m 
  => Optic (->) s s a b -> (a -> b) -> m c -> m c

data PRef c rs a = forall x . PRef (Optical' c x a) !(rs x)
-}


--instance  (forall s . MonadState s m, MonadUnliftIO m) => MonadState (PRef Mapping m a) m where

uses :: MonadState s m => AGetter a s t a b -> m a
uses l = gets (view l)

-- e.g. b -> IO () 
--c (Costar (Const b)) => PRefs c (Star m b) rs b a 
--  PRefs o _ f = f b >> return ()
tellex :: MonadWriter w m => c (Costar (Const a)) => PRef c rs b a -> a -> m () 
tellex (PRef o rs) a = undefined 

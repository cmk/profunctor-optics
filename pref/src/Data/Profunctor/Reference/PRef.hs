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
module Data.Profunctor.Reference.PRef where

import Control.Category (Category)
import Control.Monad.Reader (MonadReader(..), asks)
import Control.Monad.IO.Unlift
import Data.Functor.Contravariant.Divisible
import Data.Profunctor.Optic
import Data.Profunctor.Reference.Global
import Data.Profunctor.Reference.Types

import qualified Data.IORef as IOR
import qualified Data.StateVar as SV
import qualified Control.Monad.Trans.Reader as R


import Control.Applicative (liftA2)
import Data.IORef (IORef(..))

---------------------------------------------------------------------
--  PRef
---------------------------------------------------------------------


{- | A 'PRef' is a mutable reference bound together with a profunctor 

optic by existentializing over the 's' and 't' variables and setting 

them equal to one another. See also 'Data.Profunctor.Reference.PRefs'.

The type variables signify:

  * @c@ - The constraint determining which operations can be performed.

  * @rs@ - The read container reference (e.g. 'MVar', 'IORef' etc.).

  * @a@ - The exposed read / write type.

-}

data PRef c rs b a = forall x . PRef (Optical c x x a b) !(rs x)

type PVar c b a = PRef c StateVar b a

instance (forall s . HasGetter (rs s) s, c (Star (Const a))) => HasGetter (PRef c rs b a) a where

  get (PRef o rs) = liftIO $ view o <$> SV.get rs
  {-# INLINE get #-}

instance (forall s. HasUpdate (rs s) s s, c (->)) => HasSetter (PRef c rs b a) b where

  (PRef o rs) $= b = liftIO $ rs $~ over o (const b)
  {-# INLINE ($=) #-}

instance (forall s. HasUpdate (rs s) s s, c (->)) => HasUpdate (PRef c rs b a) a b where

  (PRef o rs) $~ f  = liftIO $ rs $~ over o f

  (PRef o rs) $~! f = liftIO $ rs $~! over o f

dimap' :: (b' -> b) -> (a -> a') -> PRef Profunctor rs b a -> PRef Profunctor rs b' a'
dimap' bs sa (PRef o rs) = PRef (o . dimap sa bs) rs

instance Profunctor (PRef Profunctor rs) where dimap = dimap'


(*$*) :: Applicative f => PRef Strong f b1 a1 -> PRef Strong f b2 a2 -> PRef Strong f (b1,b2) (a1,a2)
(*$*) (PRef o f) (PRef o' f') = PRef (paired o o') (liftA2 (,) f f')

(+$+) :: Decidable f => PRef Choice f b1 a1 -> PRef Choice f b2 a2 -> PRef Choice f (Either b1 b2) (Either a1 a2)
(+$+) (PRef o f) (PRef o' f') = PRef (split o o') (chosen f f')


-- | Unbox a 'Pxy' by providing an existentially quantified continuation.
withPRef
  :: PRef c rs b a 
  -> (forall x . Optical c x x a b -> rs x -> r) 
  -> r
withPRef (PRef o rs) f = f o rs

{-

newtype LocalRef c s a = 
  LocalRef { unLocalRef :: Ref m r => forall r. ReaderT (PRef STRef c s) (ST r) a }

-}



has :: MonadReader r m => c (Star (Const a)) => PRef c ((->) r) b a -> m a
has (PRef o rs) = view o <$> asks rs



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



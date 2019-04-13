{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE QuantifiedConstraints, ConstraintKinds     #-}

{-# OPTIONS_GHC -w #-}
module Data.Profunctor.Reference.PError where

import Control.Applicative
import Control.Exception (Exception(..), SomeException, AsyncException, ArrayException, ArithException)
import Control.Monad (MonadPlus(..))
import Control.Monad.IO.Unlift

import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible

import Data.Profunctor.Reference.Types
import Data.Profunctor.Reference.PRef
import Data.Void

import Data.Monoid

import qualified Control.Exception as Ex 
import qualified UnliftIO.Exception as Ux hiding (Handler)
import qualified Control.Exception.Optic as O 





data Handler m e = Handler { runHandler :: forall a. e -> m a }

instance Contravariant (Handler m) where
  
  contramap f (Handler h) = Handler $ h . f

instance MonadPlus m => Divisible (Handler m) where
  
  divide f (Handler h) (Handler h') = 
    Handler $ \e -> case f e of (e1, e2) -> h e1 >> h' e2
  
  conquer = Handler $ const mzero

instance MonadPlus m => Decidable (Handler m) where

  lose f = Handler $ \a -> absurd (f a)

  choose f (Handler h) (Handler h') = Handler $ either h h' . f



type PError m c a = PRef c Exception (Handler m) a a

-- | A 'PError' with no backend handler.
--
pthrow :: (MonadIO m, Exception a) => PError m Choice a
pthrow = PRef O.exception (Handler Ux.throwIO)

{-# INLINE as #-}

-- | Create a new 'PError' that acts like an 'AsPrism' typeclass.
--
-- This function takes a handler for a backend exception type @e@ 
-- and ties it to a user exception type @a@.
--
as :: (MonadIO m, Exception a, Exception s) => Prism' s a -> Handler m s -> PError m Choice a
as o h = PRef o h

-- | A variant of 'asPError' specialized to 'SomeException'.
--
asSomeException :: (MonadIO m, Exception a) => Handler m SomeException -> PError m Choice a
asSomeException h = PRef O.exception h


----------------------------------------------------------------------------------------------------
-- Arithmetic Exceptions
----------------------------------------------------------------------------------------------------

asArithException :: (MonadIO m, Exception a) => Prism' ArithException a -> Handler m ArithException -> PError m Choice a
asArithException o h = PRef o h


{-# INLINE asOverflow #-}

-- | Detect arithmetic overflow.
--
asOverflow :: MonadIO m => Handler m ArithException -> PError m Choice () 
asOverflow h = PRef O._Overflow h


{-# INLINE asUnderflow #-}

-- | Detect arithmetic underflow.
--
asUnderflow :: MonadIO m => Handler m ArithException -> PError m Choice () 
asUnderflow h = PRef O._Underflow h


{-# INLINE asLossOfPrecision #-}

-- | Detect arithmetic loss of precision.
--
asLossOfPrecision :: MonadIO m => Handler m ArithException -> PError m Choice () 
asLossOfPrecision h = PRef O._LossOfPrecision h


{-# INLINE asDivideByZero #-}

-- | Detect division by zero.
--
asDivideByZero :: MonadIO m => Handler m ArithException -> PError m Choice () 
asDivideByZero h = PRef O._DivideByZero h


{-# INLINE asDenormal #-}

-- | Detect exceptional denormalized floating pure.
--
asDenormal :: MonadIO m => Handler m ArithException -> PError m Choice () 
asDenormal h = PRef O._Denormal h


{-# INLINE asRatioZeroDenominator #-}

-- | Detect zero denominators.
--
-- Added in @base@ 4.6 in response to this libraries discussion:
--
-- <http://haskell.1045720.n5.nabble.com/Data-Ratio-and-exceptions-td5711246.html>
--
asRatioZeroDenominator :: MonadIO m => Handler m ArithException -> PError m Choice () 
asRatioZeroDenominator h = PRef O._RatioZeroDenominator h

----------------------------------------------------------------------------------------------------
-- Array Exceptions
----------------------------------------------------------------------------------------------------

asArrayException :: (MonadIO m, Exception a) => Prism' ArrayException a -> Handler m ArrayException -> PError m Choice a
asArrayException o h = PRef o h


{-# INLINE asIndexOutOfBounds #-}

-- | Detect attempts to index an array outside its declared bounds.
--
asIndexOutOfBounds :: MonadIO m => Handler m ArrayException -> PError m Choice String 
asIndexOutOfBounds h = PRef O._IndexOutOfBounds h


{-# INLINE asUndefinedElement #-}

-- | Detect attempts to evaluate an element of an array that has not been initialized.
--
asUndefinedElement :: MonadIO m => Handler m ArrayException -> PError m Choice String 
asUndefinedElement h = PRef O._UndefinedElement h


----------------------------------------------------------------------------------------------------
-- Async Exceptions
----------------------------------------------------------------------------------------------------

asAsyncException :: (MonadIO m, Exception a) => Prism' AsyncException a -> Handler m AsyncException -> PError m Choice a
asAsyncException o h = PRef o h


{-# INLINE asStackOverflow #-}

-- | The current thread's stack exceeded its limit. Since an 'Exception' has
-- been raised, the thread's stack will certainly be below its limit again,
-- but the programmer should take remedial action immediately.
--
asStackOverflow :: MonadIO m => Handler m AsyncException -> PError m Choice () 
asStackOverflow h = PRef O._StackOverflow h


{-# INLINE asHeapOverflow #-}

-- | The program's heap usage has exceeded its limit.
--
asHeapOverflow :: MonadIO m => Handler m AsyncException -> PError m Choice () 
asHeapOverflow h = PRef O._HeapOverflow h


{-# INLINE asThreadKilled #-}

-- | This 'Exception' is raised by another thread calling
-- 'Control.Concurrent.killThread', or by the system if it needs to terminate
-- the thread for some reason.
--
asThreadKilled :: MonadIO m => Handler m AsyncException -> PError m Choice () 
asThreadKilled h = PRef O._ThreadKilled h


{-# INLINE asUserInterrupt #-}

-- | This 'Exception' is raised by default in the main thread of the program when
-- the user requests to terminate the program via the usual mechanism(s)
-- (/e.g./ Control-C in the console).
--
asUserInterrupt :: MonadIO m => Handler m AsyncException -> PError m Choice () 
asUserInterrupt h = PRef O._UserInterrupt h


--
-- asArrayException
-- asAsyncException
{-
-- TODO- you can use these to define domain-level exceptions. e.g.
-- myerr :: PError IO Choice MyDomainException = perror
-- then come back and handle the backend exception hierarchy at a later time
-- 
data Foo = Foo deriving Show
instance Exception Foo

data Bar = Bar deriving Show
instance Exception Bar

foo :: PError IO Choice Foo
foo = pthrow

bar :: PError IO Choice Bar
bar = pthrow
 
baz :: PError m c a -> PRef c X (Handler m) a a
baz (PRef o h) = (PRef o h)

> :t baz foo +$+ baz bar

  :: PRef
       Choice
       X
       (Handler IO)
       (Either Foo Bar)
       (Either Foo Bar)
-}




trying :: MonadUnliftIO m => c (Star (Const (First a))) => PError m c a -> m r -> m (Either a r)
trying (PRef o _) m = O.trying o m

throwing :: MonadUnliftIO m => c (Costar (Const a)) => PError m c a -> a -> m r
throwing (PRef o _) a = O.throwing o a

-- | Catch exceptions with the backend 'Handler' or the user-supplied handler.
catching :: MonadUnliftIO m => c (Star (Either a)) => PError m c a -> m r -> (a -> m r) -> m r
catching (PRef o (Handler ht)) m ha = m `Ux.catch` \e -> either ht ha $ match o e

-- | A flipped variant of 'catchPError'.
handling :: MonadUnliftIO m => c (Star (Either a)) => PError m c a -> (a -> m r) -> m r -> m r
handling perr = flip $ catching perr





{-
data Catch m a b = forall e . Exception e => Catch (b -> Maybe e) (e -> m a)


instance Contravariant (Catch m a) where
  
  contramap f (Catch emt tma) = Catch (emt . f) tma

instance MonadThrow m => Divisible (Catch m a) where
  
  divide f (Catch g g') (Catch h h') = 
    Catch (\e -> case f e of (e1, e2) -> g e1 <|> h e2) (\t -> g' t >> h' t) --TODO 
  
  conquer = Catch (const Nothing) throwM

instance MonadThrow m => Decidable (Catch m a) where

  lose _ = Catch (const Nothing) throwM

  choose f (Catch g g') (Catch h _) = Catch (either g h . f) g' --TODO left-biased ?

data PRefs'' c rt rs b a = forall x y . Exception x => PRefs'' (Optical c x y a b) (rs x) (rt y)
--type PError c rt rs b a = PRefs c X Exception rt rs b a 

tryFoo :: MonadUnliftIO m => c (Star (Const (First a))) => PRefs'' c rt rs b a -> m r -> m (Either a r)
tryFoo (PRefs'' o _ _ ) m = tryJust (preview o) m


-- | Type alias for 'PRefs' constructed from @m s@, @(t -> Maybe e)@, and @(e -> m a)@.

type PCatch m c b a = PRefs' c (Catch m a) m b a

data PRefs' c rt rs b a = forall x y . Exception y => PRefs' (Optical c x y a b) (rs x) (rt y)

--type PCatch c rt rs b a = PRefs c Exception X rt rs b a 

tryPCatch :: MonadUnliftIO m => c (Star (Const a)) => PCatch m c b a -> m a
tryPCatch (PRefs' o m (Catch f g)) = catchJust f (view o <$> m) g

throwPCatch :: MonadUnliftIO m => c (Costar (Const b)) => PCatch m c b a -> b -> m a
throwPCatch (PRefs' o _ (Catch f g)) b = catchJust f (throwing o $ b) g
-}



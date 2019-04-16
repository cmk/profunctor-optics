{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE QuantifiedConstraints     #-}
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE ScopedTypeVariables       #-}

{-# OPTIONS_GHC -w #-}
module Data.Profunctor.Reference.PError where

import Control.Applicative
import Control.Exception (Exception(..), SomeException, AsyncException, ArrayException, ArithException)
import Control.Monad (MonadPlus(..))
import Control.Monad.IO.Unlift

import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible
import Data.Monoid (First(..))
import Data.Profunctor.Optic hiding (has)
import Data.Profunctor.Reference.Types
import Data.Profunctor.Reference.PRef
import Data.Void

import GHC.Conc (ThreadId)
import GHC.IO.Exception
import System.IO
import Foreign.C.Types

import Data.Validation
import qualified Control.Exception as Ex 
import qualified UnliftIO.Exception as Ux hiding (Error)
import qualified Control.Exception.Optic as O 


-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :m + Control.Exception
-- >>> :m + Data.Profunctor.Optic

-- | A generic container for exception handlers.
--
-- The existential quantification means that an 'Error m e' must eventually 
-- throw an exception. Typically 'e' is itself an instance of 'Exception',
-- and 'Error m e' catches a specific 'e', does some resource managment (e.g.
-- closing a file handle or other expensive resource) and re-throws.
--
data Error m e = Error { runError :: forall a. e -> m a }

instance Contravariant (Error m) where
  
  contramap f (Error h) = Error $ h . f

instance MonadPlus m => Divisible (Error m) where
  
  divide f (Error h) (Error h') = 
    Error $ \e -> case f e of (e1, e2) -> h e1 >> h' e2
  
  conquer = Error $ const mzero

instance MonadPlus m => Decidable (Error m) where

  lose f = Error $ \a -> absurd (f a)

  choose f (Error h) (Error h') = Error $ either h h' . f


infixr 2 +!+

(+!+) :: MonadPlus m => PError m Choice a -> PError m Choice b -> PError m Choice (Either a b)
(+!+) (PRef o f) (PRef o' f') = PRef (o +++ o') (f >+< f')


-- | 'PError's decouple backend exceptions and handlers from the rest of the program.
--
type PError m c a = PRef c Exception (Error m) a a

-- | A default 'PError' with no backend handler.
--
perror :: (MonadIO m, Exception a) => PError m Choice a
perror = PRef O.exception (Error Ux.throwIO)


-- | A 'PError' that converts an asynchronous frontend exception into a synchronous backend exception.
--
psync :: Exception a => Error m SomeException -> PError m InPhantom a
psync h = PRef (unto Ux.toSyncException) h


-- | A 'PError' that converts a synchronous frontend exception into an asynchronous backend exception.
--
-- For asynchronous exceptions, this is the same as 'Ex.toException'. 
-- For synchronous exceptions, this will wrap up the exception with 'Ux.AsyncExceptionWrapper'.
--
pasync :: Exception a => Error m SomeException -> PError m InPhantom a
pasync h = PRef (unto Ux.toAsyncException) h


-- | An async safe version of 'Ex.onException'.
--
-- Runs a frontend action using the backend handler for cleanup.
--
withPError :: MonadUnliftIO m => PError m c a -> m r -> m r
withPError (PRef _ (Error h)) act = Ux.withException act h


-- | A variant of 'Ex.try' that takes a 'Prism' (or any 'Fold') to select which
-- exceptions are caught. If the 'Exception' does not match the predicate, it is re-thrown.
--
-- Note that this will not catch asynchronous exceptions.
--
trying :: (MonadUnliftIO m, c (Star (Const (First a)))) => PError m c a -> m r -> m (Either a r)
trying (PRef o _) = O.trying o


-- | A variant of 'trying' that discards the specific exception thrown.
--
trying_ :: (MonadUnliftIO m, c (Star (Const (First a)))) => PError m c a -> m r -> m (Maybe r)
trying_ o m = preview right' <$> trying o m


-- | Throw an 'Exception' described by a 'PError'. Exceptions may be thrown from
-- purely functional code, but may only be caught within the 'IO' 'Monad'.
--
-- @
-- 'throwing' perr e \`seq\` x  ≡ 'throwing' perr e
-- @
--
throwing :: (MonadUnliftIO m, c (Costar (Const a))) => PError m c a -> a -> m r
throwing (PRef o _) = O.throwing o


-- | Catch exceptions with the backend 'Error' or the user-supplied handler.
--
-- Note that this will not catch asynchronous exceptions.
--
-- >>> catching (perror @IO @AssertionFailed) (assert False (return "uncaught")) $ \ _ -> return "caught"
-- "caught"
--
catching :: (MonadUnliftIO m, c (Star (Either a))) => PError m c a -> m r -> (a -> m r) -> m r
catching (PRef o (Error ht)) m ha = m `Ux.catch` \e -> either ht ha $ match o e

catching' :: (MonadUnliftIO m, c (Star (Validation a))) => PError m c a -> m r -> (a -> m r) -> m r
catching' (PRef o (Error ht)) m ha = m `Ux.catch` \e -> validation ht ha $ validateOf o e

-- | A flipped variant of 'catching'.
--
handling :: (MonadUnliftIO m, c (Star (Either a))) => PError m c a -> (a -> m r) -> m r -> m r
handling perr = flip $ catching perr


-- | Create a new 'PError' that acts like an 'AsPrism' typeclass.
--
-- This function takes a handler for a backend exception type @e@ 
-- and ties it to a user exception type @a@.
--
asException :: (MonadIO m, Exception a, Exception s) => Prism' s a -> Error m s -> PError m Choice a
asException o h = PRef o h


-- | A variant of 'asPError' specialized to 'SomeException'.
--
asSomeException :: (MonadIO m, Exception a) => Error m SomeException -> PError m Choice a
asSomeException = asException O.exception

----------------------------------------------------------------------------------------------------
-- IO Error Types
----------------------------------------------------------------------------------------------------

asIOException :: (MonadIO m, Exception a) => Prism' IOException a -> Error m IOException -> PError m Choice a
asIOException = asException

-- | Surface the exception type while hiding the handler.
--
errorType :: Error m IOException -> PError m Strong IOErrorType
errorType h = PRef O.errorType h


-- | Location where the error happened.
--
location :: Error m IOException -> PError m Strong String
location h = PRef O.location h


-- | Error type specific information.
--
description :: Error m IOException -> PError m Strong String
description h = PRef O.description h


-- | The handle used by the action flagging this error.
-- 
handle :: Error m IOException -> PError m Strong (Maybe Handle)
handle h = PRef O.handle h


-- | 'fileName' the error is related to.
--
fileName :: Error m IOException -> PError m Strong (Maybe FilePath)
fileName h = PRef O.fileName h


-- | 'errno' leading to this error, if any.
--
errno :: Error m IOException -> PError m Strong (Maybe CInt)
errno h = PRef O.errno h

----------------------------------------------------------------------------------------------------
-- Async Exceptions
----------------------------------------------------------------------------------------------------

asAsyncException :: (MonadIO m, Exception a) => Prism' AsyncException a -> Error m AsyncException -> PError m Choice a
asAsyncException o = asException o


{-# INLINE asStackOverflow #-}

-- | The current thread's stack exceeded its limit. Since an 'Exception' has
-- been raised, the thread's stack will certainly be below its limit again,
-- but the programmer should take remedial action immediately.
--
asStackOverflow :: MonadIO m => Error m AsyncException -> PError m Choice () 
asStackOverflow h = PRef O._StackOverflow h


{-# INLINE asHeapOverflow #-}

-- | The program's heap usage has exceeded its limit.
--
asHeapOverflow :: MonadIO m => Error m AsyncException -> PError m Choice () 
asHeapOverflow h = PRef O._HeapOverflow h


{-# INLINE asThreadKilled #-}

-- | This 'Exception' is raised by another thread calling
-- 'Control.Concurrent.killThread', or by the system if it needs to terminate
-- the thread for some reason.
--
asThreadKilled :: MonadIO m => Error m AsyncException -> PError m Choice () 
asThreadKilled h = PRef O._ThreadKilled h


{-# INLINE asUserInterrupt #-}

-- | This 'Exception' is raised by default in the main thread of the program when
-- the user requests to terminate the program via the usual mechanism(s)
-- (/e.g./ Control-C in the console).
--
asUserInterrupt :: MonadIO m => Error m AsyncException -> PError m Choice () 
asUserInterrupt h = PRef O._UserInterrupt h


----------------------------------------------------------------------------------------------------
-- Arithmetic Exceptions
----------------------------------------------------------------------------------------------------

asArithException :: (MonadIO m, Exception a) => Prism' ArithException a -> Error m ArithException -> PError m Choice a
asArithException = asException


{-# INLINE asOverflow #-}

-- | Detect arithmetic overflow.
--
asOverflow :: MonadIO m => Error m ArithException -> PError m Choice () 
asOverflow h = PRef O._Overflow h


{-# INLINE asUnderflow #-}

-- | Detect arithmetic underflow.
--
asUnderflow :: MonadIO m => Error m ArithException -> PError m Choice () 
asUnderflow h = PRef O._Underflow h


{-# INLINE asLossOfPrecision #-}

-- | Detect arithmetic loss of precision.
--
asLossOfPrecision :: MonadIO m => Error m ArithException -> PError m Choice () 
asLossOfPrecision h = PRef O._LossOfPrecision h


{-# INLINE asDivideByZero #-}

-- | Detect division by zero.
--
asDivideByZero :: MonadIO m => Error m ArithException -> PError m Choice () 
asDivideByZero h = PRef O._DivideByZero h


{-# INLINE asDenormal #-}

-- | Detect exceptional denormalized floating pure.
--
asDenormal :: MonadIO m => Error m ArithException -> PError m Choice () 
asDenormal h = PRef O._Denormal h


{-# INLINE asRatioZeroDenominator #-}

-- | Detect zero denominators.
--
-- Added in @base@ 4.6 in response to this libraries discussion:
--
-- <http://haskell.1045720.n5.nabble.com/Data-Ratio-and-exceptions-td5711246.html>
--
asRatioZeroDenominator :: MonadIO m => Error m ArithException -> PError m Choice () 
asRatioZeroDenominator h = PRef O._RatioZeroDenominator h

----------------------------------------------------------------------------------------------------
-- Array Exceptions
----------------------------------------------------------------------------------------------------

asArrayException :: (MonadIO m, Exception a) => Prism' ArrayException a -> Error m ArrayException -> PError m Choice a
asArrayException o = asException o


{-# INLINE asIndexOutOfBounds #-}

-- | Detect attempts to index an array outside its declared bounds.
--
asIndexOutOfBounds :: MonadIO m => Error m ArrayException -> PError m Choice String 
asIndexOutOfBounds h = PRef O._IndexOutOfBounds h


{-# INLINE asUndefinedElement #-}

-- | Detect attempts to evaluate an element of an array that has not been initialized.
--
asUndefinedElement :: MonadIO m => Error m ArrayException -> PError m Choice String 
asUndefinedElement h = PRef O._UndefinedElement h

----------------------------------------------------------------------------------------------------
-- Miscellaneous Exceptions
----------------------------------------------------------------------------------------------------

asAssertionFailed :: MonadIO m => Error m Ex.AssertionFailed -> PError m Choice String 
asAssertionFailed h = PRef O._AssertionFailed h

-- | Thrown when the runtime system detects that the computation is guaranteed
-- not to terminate. Note that there is no guarantee that the runtime system
-- will notice whether any given computation is guaranteed to terminate or not.
--
asNonTermination :: MonadIO m => Error m Ex.NonTermination -> PError m Choice ()
asNonTermination h = PRef O._NonTermination h


-- | Thrown when the program attempts to call atomically, from the
-- 'Control.Monad.STM' package, inside another call to atomically.
--
asNestedAtomically :: MonadIO m => Error m Ex.NestedAtomically -> PError m Choice ()
asNestedAtomically h = PRef O._NestedAtomically h


-- | The thread is blocked on an 'Control.Concurrent.MVar.MVar', but there
-- are no other references to the 'Control.Concurrent.MVar.MVar' so it can't
-- ever continue.
--
asBlockedIndefinitelyOnMVar :: MonadIO m => Error m Ex.BlockedIndefinitelyOnMVar -> PError m Choice ()
asBlockedIndefinitelyOnMVar h = PRef O._BlockedIndefinitelyOnMVar h


-- | The thread is waiting to retry an 'Control.Monad.STM.STM' transaction,
-- but there are no other references to any TVars involved, so it can't ever
-- continue.
--
asBlockedIndefinitelyOnSTM :: MonadIO m => Error m Ex.BlockedIndefinitelyOnSTM -> PError m Choice ()
asBlockedIndefinitelyOnSTM h = PRef O._BlockedIndefinitelyOnSTM h


-- | There are no runnable threads, so the program is deadlocked. The
-- 'Deadlock' 'Exception' is raised in the main thread only.
--
asDeadlock :: MonadIO m => Error m Ex.Deadlock -> PError m Choice ()
asDeadlock h = PRef O._Deadlock h


-- | A class method without a definition (neither a default definition,
-- nor a definition in the appropriate instance) was called.
--
asNoMethodError :: MonadIO m => Error m Ex.NoMethodError -> PError m Choice String
asNoMethodError h = PRef O._NoMethodError h


-- | A pattern match failed.
--
asPatternMatchFail :: MonadIO m => Error m Ex.PatternMatchFail -> PError m Choice String
asPatternMatchFail h = PRef O._PatternMatchFail h


-- | An uninitialised record field was used.
--
asRecConError :: MonadIO m => Error m Ex.RecConError -> PError m Choice String
asRecConError h = PRef O._RecConError h


-- | A record selector was applied to a constructor without the appropriate
-- field. This can only happen with a datatype with multiple constructors,
-- where some fields are in one constructor but not another.
--
asRecSelError :: MonadIO m => Error m Ex.RecSelError -> PError m Choice String
asRecSelError h = PRef O._RecSelError h


-- | A record update was performed on a constructor without the
-- appropriate field. This can only happen with a datatype with multiple
-- constructors, where some fields are in one constructor but not another.
--
asRecUpdError :: MonadIO m => Error m Ex.RecUpdError -> PError m Choice String
asRecUpdError h = PRef O._RecUpdError h


-- | Thrown when the user calls 'Prelude.error'.
--
asErrorCall :: MonadIO m => Error m Ex.ErrorCall -> PError m Choice String 
asErrorCall h = PRef O._ErrorCall h


-- | This thread has exceeded its allocation limit.
--
asAllocationLimitExceeded :: MonadIO m => Error m Ex.AllocationLimitExceeded -> PError m Choice ()
asAllocationLimitExceeded h = PRef O._AllocationLimitExceeded h

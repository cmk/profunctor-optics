{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
module Control.Exception.Optic (
    -- * Core optics
    exception
  , pattern Exception
  , sync
  , async
  , asyncException
  , pattern Async
    -- * Operators
  , throws
  , throws_
  , throwsTo
  , tries
  , tries_
  , catches
  , catches_
  , handles
  , handles_
    -- * Lifting
  , unlifted
  , exmapped
    -- * Utility
  , non'
    -- * IO Exceptions
  , ioException
    -- * IO Error Fields
  , ioeLocation
  , ioeDescription
  , ioeHandle
  , ioeFileName
  , ioeErrno
  , ioeErrorType
    -- * IO Error Types
  , alreadyExists
  , noSuchThing
  , resourceBusy
  , resourceExhausted
  , eof
  , illegalOperation
  , permissionDenied
  , userErrorType
  , unsatisfiedConstraints
  , systemError
  , protocolError
  , otherError
  , invalidArgument
  , inappropriateType
  , hardwareFault
  , unsupportedOperation
  , timeExpired
  , resourceVanished
  , interrupted
    -- * Async Exceptions
  , stackOverflow
  , heapOverflow
  , threadKilled
  , userInterrupt
    -- * Arithmetic Exceptions
  , overflow
  , underflow
  , lossOfPrecision
  , divideByZero
  , denormal
  , ratioZeroDenominator
    -- * Array Exceptions
  , indexOutOfBounds
  , undefinedElement
    -- * Miscellaneous Exceptions
  , illegal
  , assertionFailed
  , nonTermination
  , nestedAtomically
  , blockedIndefinitelyOnMVar
  , blockedIndefinitelyOnSTM
  , deadlock
  , noMethodError
  , patternMatchFail
  , recConError
  , recSelError
  , recUpdError
  , errorCall
  , allocationLimitExceeded
) where

import Control.Concurrent (ThreadId)
import Control.Exception (Exception(..), SomeException,
  AsyncException(..), IOException, ArithException(..), ArrayException(..))
import Control.Exception.Fault.Catch (MonadIO(..), MonadUnliftIO(..),
  isSyncException, isAsyncException, toSyncException, toAsyncException)
import qualified Control.Exception.Fault.Catch as Catch
import Data.Maybe (fromMaybe, isNothing)
import Data.Profunctor.Optic (Prism', Iso', Lens', Fold0, Colens, Optic', AReview,
  Profunctor, prism', iso, lens, only, grate, dimap, rmap, right', preview, review)
import Foreign.C.Types
import GHC.IO.Exception (IOErrorType)
import Prelude
import System.IO (Handle)
import qualified Control.Exception as Ex
import qualified GHC.IO.Exception as Ghc

---------------------------------------------------------------------
-- Core optics
---------------------------------------------------------------------

-- | A 'Prism' into an 'Exception' embedded in 'SomeException'.
--
-- >>> preview exception (toException DivideByZero) :: Maybe ArithException
-- Just DivideByZero
--
exception :: Exception a => Prism' SomeException a
exception = prism' fromException toException
{-# INLINE exception #-}

pattern Exception :: forall a. Exception a => a -> SomeException
pattern Exception e <- (preview exception -> Just e) where Exception e = review exception e

-- | A 'Prism' that selects synchronous exceptions (not async).
--
sync :: Prism' SomeException SomeException
sync = prism' (\e -> if isSyncException e then Just e else Nothing) toSyncException
{-# INLINE sync #-}

-- | A 'Prism' that selects asynchronous exceptions.
--
async :: Prism' SomeException SomeException
async = prism' (\e -> if isAsyncException e then Just e else Nothing) toAsyncException
{-# INLINE async #-}

-- | A 'Prism' into an 'AsyncException' embedded in 'SomeException'.
--
asyncException :: Exception a => Prism' SomeException a
asyncException = async . exception
{-# INLINE asyncException #-}

pattern Async :: forall a. Exception a => a -> SomeException
pattern Async e <- (preview asyncException -> Just e) where Async e = review asyncException e

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Throw an exception selected by a 'Prism'.
--
-- @
-- 'throws' 'exception' :: ('Exception' e, 'MonadIO' m) => e -> m a
-- @
--
throws :: MonadIO m => AReview SomeException e -> e -> m a
throws o = liftIO . Ex.throwIO . review o
{-# INLINE throws #-}

-- | Throw an exception selected by a unit 'Prism'.
--
throws_ :: MonadIO m => AReview SomeException () -> m a
throws_ o = throws o ()
{-# INLINE throws_ #-}

-- | Throw an exception to a thread, selected by a 'Prism'.
--
throwsTo :: MonadIO m => ThreadId -> AReview SomeException e -> e -> m ()
throwsTo tid o = liftIO . Ex.throwTo tid . review o
{-# INLINE throwsTo #-}

-- | Try an action, catching exceptions that match a 'Prism'.
--
-- @
-- 'tries' 'exception' :: ('Exception' e, 'MonadUnliftIO' m) => m a -> m ('Either' e a)
-- @
--
tries :: MonadUnliftIO m => Fold0 SomeException e -> m a -> m (Either e a)
tries o = Catch.tryJust (preview o)
{-# INLINE tries #-}

-- | Try an action, discarding the exception on failure.
--
tries_ :: MonadUnliftIO m => Fold0 SomeException e -> m a -> m (Maybe a)
tries_ o m = fmap (either (const Nothing) Just) (tries o m)
{-# INLINE tries_ #-}

-- | Catch exceptions that match a 'Prism'.
--
-- @
-- 'catches' 'exception' :: ('Exception' e, 'MonadUnliftIO' m) => m a -> (e -> m a) -> m a
-- @
--
catches :: MonadUnliftIO m => Fold0 SomeException e -> m a -> (e -> m a) -> m a
catches o = Catch.catchJust (preview o)
{-# INLINE catches #-}

-- | Catch exceptions that match a 'Prism', discarding the exception.
--
catches_ :: MonadUnliftIO m => Fold0 SomeException e -> m a -> m a -> m a
catches_ o m h = catches o m (const h)
{-# INLINE catches_ #-}

-- | Handle exceptions that match a 'Prism' (flipped 'catches').
--
handles :: MonadUnliftIO m => Fold0 SomeException e -> (e -> m a) -> m a -> m a
handles o = flip (catches o)
{-# INLINE handles #-}

-- | Handle exceptions that match a 'Prism', discarding the exception (flipped 'catches_').
--
handles_ :: MonadUnliftIO m => Fold0 SomeException e -> m a -> m a -> m a
handles_ o = flip (catches_ o)
{-# INLINE handles_ #-}

---------------------------------------------------------------------
-- Lifting
---------------------------------------------------------------------

-- | A 'Colens' bridging a 'MonadUnliftIO' monad and 'IO'.
--
-- @
-- 'unlifted' :: 'MonadUnliftIO' m => 'Colens' (m a) (m b) ('IO' a) ('IO' b)
-- @
--
unlifted :: MonadUnliftIO m => Colens (m a) (m b) (IO a) (IO b)
unlifted = grate (\k -> withRunInIO (\run -> k run))
{-# INLINE unlifted #-}

-- | Map one exception type to another.
--
exmapped :: (Exception e1, Exception e2, MonadUnliftIO m) => Prism' SomeException e1 -> Prism' SomeException e2 -> (e1 -> e2) -> m a -> m a
exmapped o1 o2 f = catches o1 `flip` (throws o2 . f)
{-# INLINE exmapped #-}

---------------------------------------------------------------------
-- Utility
---------------------------------------------------------------------

-- | Generate an isomorphism between @'Maybe' (a | 'isnt' p a)@ and @a@.
--
-- @'non'' p@ generalizes @'non' (p # ())@ to take any unit 'Prism'
--
non' :: Prism' a () -> Iso' (Maybe a) a
non' p = iso (fromMaybe def) go where
  def                              = review p ()
  go b | isNothing (preview p b)   = Just b
       | otherwise                 = Nothing
{-# INLINE non' #-}

---------------------------------------------------------------------
-- IO Exceptions
---------------------------------------------------------------------

-- | Prism into 'IOException' from 'SomeException'.
--
ioException :: Prism' SomeException IOException
ioException = exception
{-# INLINE ioException #-}

-- | Where the error happened.
--
ioeLocation :: Lens' IOException String
ioeLocation = lens Ghc.ioe_location $ \s e -> s { Ghc.ioe_location = e }

-- | Error type specific information.
--
ioeDescription :: Lens' IOException String
ioeDescription = lens Ghc.ioe_description $ \s e -> s { Ghc.ioe_description = e }

-- | The handle used by the action flagging this error.
--
ioeHandle :: Lens' IOException (Maybe Handle)
ioeHandle = lens Ghc.ioe_handle $ \s e -> s { Ghc.ioe_handle = e }

-- | 'fileName' the error is related to.
--
ioeFileName :: Lens' IOException (Maybe FilePath)
ioeFileName = lens Ghc.ioe_filename $ \s e -> s { Ghc.ioe_filename = e }

-- | 'errno' leading to this error, if any.
--
ioeErrno :: Lens' IOException (Maybe CInt)
ioeErrno = lens Ghc.ioe_errno $ \s e -> s { Ghc.ioe_errno = e }

-- | The type of IO error.
--
ioeErrorType :: Lens' IOException IOErrorType
ioeErrorType = lens Ghc.ioe_type $ \s e -> s { Ghc.ioe_type = e }

---------------------------------------------------------------------
-- IO Error Types
---------------------------------------------------------------------

alreadyExists :: Prism' IOErrorType ()
alreadyExists = only Ghc.AlreadyExists

noSuchThing :: Prism' IOErrorType ()
noSuchThing = only Ghc.NoSuchThing

resourceBusy :: Prism' IOErrorType ()
resourceBusy = only Ghc.ResourceBusy

resourceExhausted :: Prism' IOErrorType ()
resourceExhausted = only Ghc.ResourceExhausted

eof :: Prism' IOErrorType ()
eof = only Ghc.EOF

illegalOperation :: Prism' IOErrorType ()
illegalOperation = only Ghc.IllegalOperation

permissionDenied :: Prism' IOErrorType ()
permissionDenied = only Ghc.PermissionDenied

userErrorType :: Prism' IOErrorType ()
userErrorType = only Ghc.UserError

unsatisfiedConstraints :: Prism' IOErrorType ()
unsatisfiedConstraints = only Ghc.UnsatisfiedConstraints

systemError :: Prism' IOErrorType ()
systemError = only Ghc.SystemError

protocolError :: Prism' IOErrorType ()
protocolError = only Ghc.ProtocolError

otherError :: Prism' IOErrorType ()
otherError = only Ghc.OtherError

invalidArgument :: Prism' IOErrorType ()
invalidArgument = only Ghc.InvalidArgument

inappropriateType :: Prism' IOErrorType ()
inappropriateType = only Ghc.InappropriateType

hardwareFault :: Prism' IOErrorType ()
hardwareFault = only Ghc.HardwareFault

unsupportedOperation :: Prism' IOErrorType ()
unsupportedOperation = only Ghc.UnsupportedOperation

timeExpired :: Prism' IOErrorType ()
timeExpired = only Ghc.TimeExpired

resourceVanished :: Prism' IOErrorType ()
resourceVanished = only Ghc.ResourceVanished

interrupted :: Prism' IOErrorType ()
interrupted = only Ghc.Interrupted

---------------------------------------------------------------------
-- Async Exceptions
---------------------------------------------------------------------

stackOverflow :: Prism' AsyncException ()
stackOverflow = only Ex.StackOverflow

heapOverflow :: Prism' AsyncException ()
heapOverflow = only Ex.HeapOverflow

threadKilled :: Prism' AsyncException ()
threadKilled = only Ex.ThreadKilled

userInterrupt :: Prism' AsyncException ()
userInterrupt = only Ex.UserInterrupt

---------------------------------------------------------------------
-- Arithmetic Exceptions
---------------------------------------------------------------------

overflow :: Prism' ArithException ()
overflow = only Ex.Overflow

underflow :: Prism' ArithException ()
underflow = only Ex.Underflow

lossOfPrecision :: Prism' ArithException ()
lossOfPrecision = only Ex.LossOfPrecision

divideByZero :: Prism' ArithException ()
divideByZero = only Ex.DivideByZero

denormal :: Prism' ArithException ()
denormal = only Ex.Denormal

ratioZeroDenominator :: Prism' ArithException ()
ratioZeroDenominator = only Ex.RatioZeroDenominator

---------------------------------------------------------------------
-- Array Exceptions
---------------------------------------------------------------------

-- | Detect attempts to index an array outside its declared bounds.
--
indexOutOfBounds :: Prism' ArrayException String
indexOutOfBounds = dimap sta (either id id) . right' . rmap Ex.IndexOutOfBounds
  where sta (Ex.IndexOutOfBounds r) = Right r
        sta t = Left t

-- | Detect attempts to evaluate an element of an array that has not been initialized.
--
undefinedElement :: Prism' ArrayException String
undefinedElement = dimap sta (either id id) . right' . rmap Ex.UndefinedElement
  where sta (Ex.UndefinedElement r) = Right r
        sta t = Left t

---------------------------------------------------------------------
-- Miscellaneous Exceptions
---------------------------------------------------------------------

-- | Construct an optic for an exception type without an 'Eq' instance.
--
illegal :: Profunctor p => t -> Optic' p t ()
illegal t = const () `dimap` const t

assertionFailed :: Prism' Ex.AssertionFailed String
assertionFailed = iso (\(Ex.AssertionFailed a) -> a) Ex.AssertionFailed

nonTermination :: Prism' Ex.NonTermination ()
nonTermination = illegal Ex.NonTermination

nestedAtomically :: Prism' Ex.NestedAtomically ()
nestedAtomically = illegal Ex.NestedAtomically

blockedIndefinitelyOnMVar :: Prism' Ex.BlockedIndefinitelyOnMVar ()
blockedIndefinitelyOnMVar = illegal Ex.BlockedIndefinitelyOnMVar

blockedIndefinitelyOnSTM :: Prism' Ex.BlockedIndefinitelyOnSTM ()
blockedIndefinitelyOnSTM = illegal Ex.BlockedIndefinitelyOnSTM

deadlock :: Prism' Ex.Deadlock ()
deadlock = illegal Ex.Deadlock

noMethodError :: Prism' Ex.NoMethodError String
noMethodError = iso (\(Ex.NoMethodError a) -> a) Ex.NoMethodError

patternMatchFail :: Prism' Ex.PatternMatchFail String
patternMatchFail = iso (\(Ex.PatternMatchFail a) -> a) Ex.PatternMatchFail

recConError :: Prism' Ex.RecConError String
recConError = iso (\(Ex.RecConError a) -> a) Ex.RecConError

recSelError :: Prism' Ex.RecSelError String
recSelError = iso (\(Ex.RecSelError a) -> a) Ex.RecSelError

recUpdError :: Prism' Ex.RecUpdError String
recUpdError = iso (\(Ex.RecUpdError a) -> a) Ex.RecUpdError

errorCall :: Prism' Ex.ErrorCall String
errorCall = iso (\(Ex.ErrorCall a) -> a) Ex.ErrorCall

allocationLimitExceeded :: Prism' Ex.AllocationLimitExceeded ()
allocationLimitExceeded = illegal Ex.AllocationLimitExceeded

{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
module Control.Exception.Optic (
    -- * Common optics
    non'
  , unlifted
  , exmapped
  , exception
  , pattern Exception
    -- * Derived operators
  , throws
  , throws_
  , throwsTo
  , tries
  , tries_
  , catches
  , catches_
  , handles
  , handles_
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
  , userError
  , unsatisfiedConstraints
  , systemError
  , protocolError
  , otherError
  , invalidArgument
  , inappropriateType
  , hardwareFault
  , unsupportedOperation
    -- * Async Exceptions
  , sync
  , async
  , asyncException
  , pattern AsyncException
  , timeExpired
  , resourceVanished
  , interrupted
  , stackOverflow
  , heapOverflow
  , threadKilled
  , userInterrupt 
    -- * Arithmetic exceptions
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

import Control.Exception (Exception(..), SomeException, 
  AsyncException(..), IOException, ArithException(..), ArrayException(..))
import Data.Maybe (fromMaybe)
import Data.Profunctor.Optic
import Data.Profunctor.Optic.Import
import Foreign.C.Types
import GHC.IO.Exception (IOErrorType)
import System.IO
import Prelude (String)
import qualified Control.Exception as Ex 
import qualified GHC.IO.Exception as Ghc

pattern Exception :: forall a. Exception a => a -> SomeException
pattern Exception e <- (preview exception -> Just e) where Exception e = review exception e

pattern AsyncException :: forall a. Exception a => a -> SomeException
pattern AsyncException e <- (preview asyncException -> Just e) where AsyncException e = review asyncException e

-- | Generate an isomorphism between @'Maybe' (a | 'isnt' p a)@ and @a@.
--
-- @'non'' p@ generalizes @'non' (p # ())@ to take any unit 'Prism'
--
non' :: Prism' a () -> Iso' (Maybe a) a
non' p = iso (fromMaybe def) go where
  def               = review p ()
  go b | p `isnt` b = Just b
       | otherwise  = Nothing
{-# INLINE non' #-}

----------------------------------------------------------------------------------------------------
-- IO Exceptions
----------------------------------------------------------------------------------------------------

-- | Exceptions that occur in the 'IO' 'Monad'. 
--
-- An 'IOException' records a more specific error type, a descriptive string and possibly the handle 
-- that was used when the error was flagged.
--
ioException :: Prism' SomeException IOException
ioException = exception

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

ioeErrorType :: Lens' IOException IOErrorType
ioeErrorType = lens Ghc.ioe_type $ \s e -> s { Ghc.ioe_type = e }

----------------------------------------------------------------------------------------------------
-- IO Error Types
----------------------------------------------------------------------------------------------------

-- | TODO: Document
--
alreadyExists :: Prism' IOErrorType ()
alreadyExists = only Ghc.AlreadyExists

-- | TODO: Document
--
noSuchThing :: Prism' IOErrorType ()
noSuchThing = only Ghc.NoSuchThing

-- | TODO: Document
--
resourceBusy :: Prism' IOErrorType ()
resourceBusy = only Ghc.ResourceBusy

-- | TODO: Document
--
resourceExhausted :: Prism' IOErrorType ()
resourceExhausted = only Ghc.ResourceExhausted

-- | TODO: Document
--
eof :: Prism' IOErrorType ()
eof = only Ghc.EOF

-- | TODO: Document
--
illegalOperation :: Prism' IOErrorType ()
illegalOperation = only Ghc.IllegalOperation

-- | TODO: Document
--
permissionDenied :: Prism' IOErrorType ()
permissionDenied = only Ghc.PermissionDenied

-- | TODO: Document
--
userError :: Prism' IOErrorType ()
userError = only Ghc.UserError

-- | TODO: Document
--
unsatisfiedConstraints :: Prism' IOErrorType ()
unsatisfiedConstraints = only Ghc.UnsatisfiedConstraints

-- | TODO: Document
--
systemError :: Prism' IOErrorType ()
systemError = only Ghc.SystemError

-- | TODO: Document
--
protocolError :: Prism' IOErrorType ()
protocolError = only Ghc.ProtocolError

-- | TODO: Document
--
otherError :: Prism' IOErrorType ()
otherError = only Ghc.OtherError

-- | TODO: Document
--
invalidArgument :: Prism' IOErrorType ()
invalidArgument = only Ghc.InvalidArgument

-- | TODO: Document
--
inappropriateType :: Prism' IOErrorType ()
inappropriateType = only Ghc.InappropriateType

-- | TODO: Document
--
hardwareFault :: Prism' IOErrorType ()
hardwareFault = only Ghc.HardwareFault

-- | TODO: Document
--
unsupportedOperation :: Prism' IOErrorType ()
unsupportedOperation = only Ghc.UnsupportedOperation

-- | TODO: Document
--
timeExpired :: Prism' IOErrorType ()
timeExpired = only Ghc.TimeExpired

-- | TODO: Document
--
resourceVanished :: Prism' IOErrorType ()
resourceVanished = only Ghc.ResourceVanished

-- | TODO: Document
--
interrupted :: Prism' IOErrorType ()
interrupted = only Ghc.Interrupted

----------------------------------------------------------------------------------------------------
-- Async Exceptions
----------------------------------------------------------------------------------------------------

-- | The current thread's stack exceeded its limit. Since an 'Exception' has
-- been raised, the thread's stack will certainly be below its limit again,
-- but the programmer should take remedial action immediately.
--
stackOverflow :: Prism' AsyncException ()
stackOverflow = only Ex.StackOverflow

-- | The program's heap usage has exceeded its limit.
--
-- See 'GHC.IO.Exception' for more information.
-- 
heapOverflow :: Prism' AsyncException ()
heapOverflow = only Ex.HeapOverflow

-- | This 'Exception' is raised by another thread calling
-- 'Control.Concurrent.killThread', or by the system if it needs to terminate
-- the thread for some reason.
--
threadKilled :: Prism' AsyncException ()
threadKilled = only Ex.ThreadKilled

-- | This 'Exception' is raised by default in the main thread of the program when
-- the user requests to terminate the program via the usual mechanism(s)
-- (/e.g./ Control-C in the console).
--
userInterrupt :: Prism' AsyncException ()
userInterrupt = only Ex.UserInterrupt

----------------------------------------------------------------------------------------------------
-- Arithmetic exceptions
----------------------------------------------------------------------------------------------------

-- | Detect arithmetic overflow.
--
overflow :: Prism' ArithException ()
overflow = only Ex.Overflow

-- | Detect arithmetic underflow.
--
underflow :: Prism' ArithException ()
underflow = only Ex.Underflow

-- | Detect arithmetic loss of precision.
--
lossOfPrecision :: Prism' ArithException ()
lossOfPrecision = only Ex.LossOfPrecision

-- | Detect division by zero.
--
divideByZero :: Prism' ArithException ()
divideByZero = only Ex.DivideByZero

-- | Detect whether a FLOP was performed on a subnormal number. 
--
denormal :: Prism' ArithException ()
denormal = only Ex.Denormal

-- | Detect zero denominators.
--
ratioZeroDenominator :: Prism' ArithException ()
ratioZeroDenominator = only Ex.RatioZeroDenominator

----------------------------------------------------------------------------------------------------
-- Array Exceptions
----------------------------------------------------------------------------------------------------

-- | Detect attempts to index an array outside its declared bounds.
--
indexOutOfBounds :: Prism' ArrayException String
indexOutOfBounds = dimap sta join . right' . rmap Ex.IndexOutOfBounds
  where sta (Ex.IndexOutOfBounds r) = Right r
        sta t = Left t

-- | Detect attempts to evaluate an element of an array that has not been initialized.
--
undefinedElement :: Prism' ArrayException String
undefinedElement = dimap sta join . right' . rmap Ex.UndefinedElement
  where sta (Ex.UndefinedElement r) = Right r
        sta t = Left t

----------------------------------------------------------------------------------------------------
-- Miscellaneous Exceptions
----------------------------------------------------------------------------------------------------

-- hack to get prisms for exceptions w/o an Eq instance 
illegal :: Profunctor p => t -> Optic' p t ()
illegal t = const () `dimap` const t

assertionFailed :: Prism' Ex.AssertionFailed String
assertionFailed = iso (\(Ex.AssertionFailed a) -> a) Ex.AssertionFailed

-- | Thrown when the runtime system detects that the computation is guaranteed
-- not to terminate. Note that there is no guarantee that the runtime system
-- will notice whether any given computation is guaranteed to terminate or not.
--
nonTermination :: Prism' Ex.NonTermination ()
nonTermination = illegal Ex.NonTermination

-- | Thrown when the program attempts to call atomically, from the
-- 'Control.Monad.STM' package, inside another call to atomically.
--
nestedAtomically :: Prism' Ex.NestedAtomically ()
nestedAtomically = illegal Ex.NestedAtomically

-- | The thread is blocked on an 'Control.Concurrent.MVar.MVar', but there
-- are no other references to the 'Control.Concurrent.MVar.MVar' so it can't
-- ever continue.
--
blockedIndefinitelyOnMVar :: Prism' Ex.BlockedIndefinitelyOnMVar ()
blockedIndefinitelyOnMVar = illegal Ex.BlockedIndefinitelyOnMVar

-- | The thread is waiting to retry an 'Control.Monad.STM.STM' transaction,
-- but there are no other references to any TVars involved, so it can't ever
-- continue.
--
blockedIndefinitelyOnSTM :: Prism' Ex.BlockedIndefinitelyOnSTM ()
blockedIndefinitelyOnSTM = illegal Ex.BlockedIndefinitelyOnSTM

-- | There are no runnable threads, so the program is deadlocked. The
-- 'Deadlock' 'Exception' is raised in the main thread only.
--
deadlock :: Prism' Ex.Deadlock ()
deadlock = illegal Ex.Deadlock

-- | A class method without a definition (neither a default definition,
-- nor a definition in the appropriate instance) was called.
--
noMethodError :: Prism' Ex.NoMethodError String
noMethodError = iso (\(Ex.NoMethodError a) -> a) Ex.NoMethodError

-- | A pattern match failed.
--
patternMatchFail :: Prism' Ex.PatternMatchFail String
patternMatchFail = iso (\(Ex.PatternMatchFail a) -> a) Ex.PatternMatchFail

-- | An uninitialised record field was used.
--
recConError :: Prism' Ex.RecConError String
recConError = iso (\(Ex.RecConError a) -> a) Ex.RecConError

-- | A record selector was applied to a constructor without the appropriate
-- field. This can only happen with a datatype with multiple constructors,
-- where some fields are in one constructor but not another.
--
recSelError :: Prism' Ex.RecSelError String
recSelError = iso (\(Ex.RecSelError a) -> a) Ex.RecSelError

-- | A record update was performed on a constructor without the
-- appropriate field. This can only happen with a datatype with multiple
-- constructors, where some fields are in one constructor but not another.
--
recUpdError :: Prism' Ex.RecUpdError String
recUpdError = iso (\(Ex.RecUpdError a) -> a) Ex.RecUpdError

-- | Thrown when the user calls 'Prelude.error'.
--
errorCall :: Prism' Ex.ErrorCall String
errorCall = iso (\(Ex.ErrorCall a) -> a) Ex.ErrorCall

-- | This thread has exceeded its allocation limit.
--
allocationLimitExceeded :: Prism' Ex.AllocationLimitExceeded ()
allocationLimitExceeded = illegal Ex.AllocationLimitExceeded

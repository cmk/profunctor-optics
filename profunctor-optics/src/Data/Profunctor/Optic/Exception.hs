module Data.Profunctor.Optic.Exception(
    exception
  , ioException
    -- * IO Error Fields
  , location
  , description
  , handle
  , fileName
  , errno
  , errorType
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
  , trivial 
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

import Control.Exception hiding (handle)
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Iso
import Data.Profunctor.Optic.Lens
import Data.Profunctor.Optic.Prism
import Data.Profunctor.Optic.Type
import Foreign.C.Types
import GHC.IO.Exception (IOErrorType)
import System.IO
import qualified Control.Exception as Ex 
import qualified GHC.IO.Exception as Ghc

----------------------------------------------------------------------------------------------------
-- IO Exceptions
----------------------------------------------------------------------------------------------------

-- | Where the error happened.
--
location :: Lens' IOException String
location = lens Ghc.ioe_location $ \s e -> s { Ghc.ioe_location = e }

-- | Error type specific information.
--
description :: Lens' IOException String
description = lens Ghc.ioe_description $ \s e -> s { Ghc.ioe_description = e }

-- | The handle used by the action flagging this error.
-- 
handle :: Lens' IOException (Maybe Handle)
handle = lens Ghc.ioe_handle $ \s e -> s { Ghc.ioe_handle = e }

-- | 'fileName' the error is related to.
--
fileName :: Lens' IOException (Maybe FilePath)
fileName = lens Ghc.ioe_filename $ \s e -> s { Ghc.ioe_filename = e }

-- | 'errno' leading to this error, if any.
--
errno :: Lens' IOException (Maybe CInt)
errno = lens Ghc.ioe_errno $ \s e -> s { Ghc.ioe_errno = e }

errorType :: Lens' IOException IOErrorType
errorType = lens Ghc.ioe_type $ \s e -> s { Ghc.ioe_type = e }

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
stackOverflow = dimap sta (either id id) . right' . rmap (const Ex.StackOverflow)
  where sta Ex.StackOverflow = Right ()
        sta t = Left t

-- | The program's heap usage has exceeded its limit.
--
-- See 'GHC.IO.Exception' for more information.
-- 
heapOverflow :: Prism' AsyncException ()
heapOverflow = dimap sta (either id id) . right' . rmap (const Ex.HeapOverflow)
  where sta Ex.HeapOverflow = Right ()
        sta t = Left t

-- | This 'Exception' is raised by another thread calling
-- 'Control.Concurrent.killThread', or by the system if it needs to terminate
-- the thread for some reason.
--
threadKilled :: Prism' AsyncException ()
threadKilled = dimap sta (either id id) . right' . rmap (const Ex.ThreadKilled)
  where sta Ex.ThreadKilled = Right ()
        sta t = Left t

-- | This 'Exception' is raised by default in the main thread of the program when
-- the user requests to terminate the program via the usual mechanism(s)
-- (/e.g./ Control-C in the console).
--
userInterrupt :: Prism' AsyncException ()
userInterrupt = dimap sta (either id id) . right' . rmap (const Ex.UserInterrupt)
  where sta Ex.UserInterrupt = Right ()
        sta t = Left t

----------------------------------------------------------------------------------------------------
-- Arithmetic exceptions
----------------------------------------------------------------------------------------------------

-- | Detect arithmetic overflow.
--
overflow :: Prism' ArithException ()
overflow = dimap sta (either id id) . right' . rmap (const Ex.Overflow)
  where sta Ex.Overflow = Right ()
        sta t = Left t

-- | Detect arithmetic underflow.
--
underflow :: Prism' ArithException ()
underflow = dimap sta (either id id) . right' . rmap (const Ex.Underflow)
  where sta Ex.Underflow = Right ()
        sta t = Left t

-- | Detect arithmetic loss of precision.
--
lossOfPrecision :: Prism' ArithException ()
lossOfPrecision = dimap sta (either id id) . right' . rmap (const Ex.LossOfPrecision)
  where sta Ex.LossOfPrecision = Right ()
        sta t = Left t

-- | Detect division by zero.
--
divideByZero :: Prism' ArithException ()
divideByZero = dimap sta (either id id) . right' . rmap (const Ex.DivideByZero)
  where sta Ex.DivideByZero = Right ()
        sta t = Left t

-- | Detect exceptional denormalized floating pure.
--
denormal :: Prism' ArithException ()
denormal = dimap sta (either id id) . right' . rmap (const Ex.Denormal)
  where sta Ex.Denormal = Right ()
        sta t = Left t

-- | Detect zero denominators.
--
-- Added in @base@ 4.6 in response to this libraries discussion:
--
-- <http://haskell.1045720.n5.nabble.com/Data-Ratio-and-exceptions-td5711246.html>
--
ratioZeroDenominator :: Prism' ArithException ()
ratioZeroDenominator = dimap sta (either id id) . right' . rmap (const Ex.RatioZeroDenominator)
  where sta Ex.RatioZeroDenominator = Right ()
        sta t = Left t

----------------------------------------------------------------------------------------------------
-- Array Exceptions
----------------------------------------------------------------------------------------------------

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

----------------------------------------------------------------------------------------------------
-- Miscellaneous Exceptions
----------------------------------------------------------------------------------------------------

trivial :: Profunctor p => t -> Optic' p t ()
trivial t = const () `dimap` const t

assertionFailed :: Prism' Ex.AssertionFailed String
assertionFailed = iso (\(Ex.AssertionFailed a) -> a) Ex.AssertionFailed

-- | Thrown when the runtime system detects that the computation is guaranteed
-- not to terminate. Note that there is no guarantee that the runtime system
-- will notice whether any given computation is guaranteed to terminate or not.
--
nonTermination :: Prism' Ex.NonTermination ()
nonTermination = trivial Ex.NonTermination

-- | Thrown when the program attempts to call atomically, from the
-- 'Control.Monad.STM' package, inside another call to atomically.
--
nestedAtomically :: Prism' Ex.NestedAtomically ()
nestedAtomically = trivial Ex.NestedAtomically

-- | The thread is blocked on an 'Control.Concurrent.MVar.MVar', but there
-- are no other references to the 'Control.Concurrent.MVar.MVar' so it can't
-- ever continue.
--
blockedIndefinitelyOnMVar :: Prism' Ex.BlockedIndefinitelyOnMVar ()
blockedIndefinitelyOnMVar = trivial Ex.BlockedIndefinitelyOnMVar

-- | The thread is waiting to retry an 'Control.Monad.STM.STM' transaction,
-- but there are no other references to any TVars involved, so it can't ever
-- continue.
--
blockedIndefinitelyOnSTM :: Prism' Ex.BlockedIndefinitelyOnSTM ()
blockedIndefinitelyOnSTM = trivial Ex.BlockedIndefinitelyOnSTM

-- | There are no runnable threads, so the program is deadlocked. The
-- 'Deadlock' 'Exception' is raised in the main thread only.
--
deadlock :: Prism' Ex.Deadlock ()
deadlock = trivial Ex.Deadlock

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
allocationLimitExceeded = trivial AllocationLimitExceeded

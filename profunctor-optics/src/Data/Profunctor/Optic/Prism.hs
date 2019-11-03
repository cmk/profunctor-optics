module Data.Profunctor.Optic.Prism where

import Control.Exception (Exception(..), SomeException, AsyncException, ArrayException, ArithException)
import Control.Monad (guard)
import Data.Profunctor.Optic.Prelude 
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Iso

import GHC.Conc (ThreadId)
import GHC.IO.Exception
import System.IO

import qualified Control.Exception as Ex 

---------------------------------------------------------------------
-- 'Prism'
---------------------------------------------------------------------

-- | Build a 'Choice' optic from a constructor and a matcher function.
--
-- \( \quad \mathsf{Prism}\;S\;A = \exists D, S \cong D + A \)
--
-- /Caution/: In order for the generated prism family to be well-defined,
-- you must ensure that the three prism laws hold:
--
-- * @seta (bt b) ≡ Right b@
--
-- * @(id ||| bt) (seta s) ≡ s@
--
-- * @left seta (seta s) ≡ left Left (seta s)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
prism :: (s -> t + a) -> (b -> t) -> Prism s t a b
prism seta bt = dimap seta (id ||| bt) . pright

-- | Create a 'Prism' from a reviewer and a matcher function that produces a 'Maybe'.
--
prism' :: (s -> Maybe a) -> (a -> s) -> Prism' s a
prism' sma as = flip prism as $ \s -> maybe (Left s) Right (sma s)

-- | Build a 'Prism' from its free tensor representation.
--
-- Useful for constructing prisms from try and handle functions.
--
handling :: (s -> e + a) -> (e + b -> t) -> Prism s t a b
handling sea ebt = dimap sea ebt . pright

-- | Build a 'Cochoice' optic from a constructor and a matcher function.
--
-- * @reprism f g ≡ \f g -> re (prism f g)@
-- 
-- * @view . re $ prism bat _ ≡ bat@
--
-- * @matchOf . re . re $ prism _ sa ≡ sa@
-- 
-- A 'Reprism' is a 'View', so you can specialise types to obtain:
--
-- @ view :: 'Reprism'' s a -> s -> a @
--
reprism :: (b -> a + t) -> (s -> a) -> Reprism s t a b
reprism beat sa = unright . dimap (id ||| sa) beat

clonePrism :: APrism s t a b -> Prism s t a b
clonePrism o = withPrism o prism

---------------------------------------------------------------------
-- 'PrismRep'
---------------------------------------------------------------------

type APrism s t a b = Optic (PrismRep a b) s t a b

type APrism' s a = APrism s s a a

-- | The 'PrismRep' profunctor precisely characterizes a 'Prism'.
data PrismRep a b s t = PrismRep (s -> t + a) (b -> t)

instance Functor (PrismRep a b s) where

  fmap f (PrismRep seta bt) = PrismRep (either (Left . f) Right . seta) (f . bt)
  {-# INLINE fmap #-}

instance Profunctor (PrismRep a b) where

  dimap f g (PrismRep seta bt) = PrismRep (either (Left . g) Right . seta . f) (g . bt)
  {-# INLINE dimap #-}

  lmap f (PrismRep seta bt) = PrismRep (seta . f) bt
  {-# INLINE lmap #-}

  rmap f (PrismRep seta bt) = PrismRep (either (Left . f) Right . seta) (f . bt)
  {-# INLINE rmap #-}

instance Choice (PrismRep a b) where

  left' (PrismRep seta bt) = PrismRep (either (either (Left . Left) Right . seta) (Left . Right)) (Left . bt)
  {-# INLINE left' #-}

  right' (PrismRep seta bt) = PrismRep (either (Left . Left) (either (Left . Right) Right . seta)) (Right . bt)
  {-# INLINE right' #-}

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

withPrism :: APrism s t a b -> ((s -> t + a) -> (b -> t) -> r) -> r
withPrism o f = case o (PrismRep Right id) of PrismRep g h -> f g h

-- | Analogous to @(+++)@ from 'Control.Arrow'
--
splitting :: Prism s1 t1 a1 b1 -> Prism s2 t2 a2 b2 -> Prism (s1 + s2) (t1 + t2) (a1 + a2) (b1 + b2) 
splitting = split

prismr :: (s -> t + a) -> (b -> t) -> Prism (c + s) (d + t) (c + a) (d + b)
prismr f g = between runSplit Split (prism f g)

-- | Use a 'Prism' to lift part of a structure.
--
aside :: APrism s t a b -> Prism (e , s) (e , t) (e , a) (e , b)
aside k =
  withPrism k $ \seta bt ->
    flip prism (fmap bt) $ \(e,s) ->
      case seta s of
        Left t  -> Left  (e,t)
        Right a -> Right (e,a)
{-# INLINE aside #-}

-- | Given a pair of prisms, project sums.
without :: APrism s t a b -> APrism u v c d -> Prism (s + u) (t + v) (a + c) (b + d)
without k =
  withPrism k $ \seta bt k' ->
    withPrism k' $ \uevc dv ->
      flip prism (bimap bt dv) $ \su ->
        case su of
          Left s  -> bimap Left Left (seta s)
          Right u -> bimap Right Right (uevc u)
{-# INLINE without #-}

-- | 'lift' a 'Prism' through a 'Traversable' functor, 
-- giving a Prism that matches only if all the elements of the container
-- matchOf the 'Prism'.
--
-- >>> [Left 1, Right "foo", Left 4, Right "woot"]^..below _R
-- []
--
-- >>> [Right "hail hydra!", Right "foo", Right "blah", Right "woot"]^..below _R
-- [["hail hydra!","foo","blah","woot"]]
below :: Traversable f => APrism' s a -> Prism' (f s) (f a)
below k =
  withPrism k $ \seta bt ->
    flip prism (fmap bt) $ \s ->
      case traverse seta s of
        Left _  -> Left s
        Right t -> Right t
{-# INLINE below #-}

---------------------------------------------------------------------
-- Common prisms
---------------------------------------------------------------------

-- | TODO: Document
--
_L :: Prism (a + c) (b + c) a b
_L = pleft

-- | TODO: Document
--
_R :: Prism (c + a) (c + b) a b
_R = pright

-- | TODO: Document
--
lowerL :: Iso s t (a + c) (b + c) -> Prism s t a b
lowerL = (. _L)

-- | TODO: Document
--
lowerR :: Iso s t (c + a) (c + b) -> Prism s t a b
lowerR = (. _R)

-- | Obtain a 'Prism' that can be composed with to filter another 'Lens', 'Iso', 'View', 'Fold' (or 'Traversal').
--
-- >>> [1..10] ^.. folded . filtered even
-- [2,4,6,8,10]
--
filtered :: (a -> Bool) -> Prism' a a
filtered f = iso (branch' f) dedup . _R 

-- | TODO: Document
--
selected :: Eq k => k -> Prism' (k , v) v
selected i = flip prism ((,) i) $ \kv@(k,v) -> branch (==i) kv v k

-- | Create a 'Prism' from a value and a predicate.
nearly ::  a -> (a -> Bool) -> Prism' a ()
nearly x f = prism' (guard . f) (const x)

-- | 'only' focuses not just on a case, but a specific value of that case.
only :: Eq a => a -> Prism' a ()
only x = nearly x (x==)

lessThan :: Bounded s => Ord s => s -> Prism' s Ordering
lessThan s = flip prism' (const s) $ \s' -> if s' < s then Just LT else Nothing  

-- | Prism for the `Just` constructor of `Maybe`.
_Just :: Prism (Maybe a) (Maybe b) a b
_Just = flip prism Just $ maybe (Left Nothing) Right

-- | Prism for the `Nothing` constructor of `Maybe`.
_Nothing :: Prism (Maybe a) (Maybe b) () ()
_Nothing = flip prism  (const Nothing) $ maybe (Right ()) (const $ Left Nothing)

excepted :: Exception a => Prism' SomeException a
excepted = prism' fromException toException

-- | Exceptions that occur in the 'IO' 'Monad'. 
--
-- An 'IOException' records a more specific error type, a descriptive string and possibly the handle 
-- that was used when the error was flagged.
--
_IOException :: Prism' SomeException IOException
_IOException = excepted

----------------------------------------------------------------------------------------------------
-- IO Error Types
----------------------------------------------------------------------------------------------------

_AlreadyExists :: Prism' IOErrorType ()
_AlreadyExists = only AlreadyExists

_NoSuchThing :: Prism' IOErrorType ()
_NoSuchThing = only NoSuchThing

_ResourceBusy :: Prism' IOErrorType ()
_ResourceBusy = only ResourceBusy

_ResourceExhausted :: Prism' IOErrorType ()
_ResourceExhausted = only ResourceExhausted

_EOF :: Prism' IOErrorType ()
_EOF = only EOF

_IllegalOperation :: Prism' IOErrorType ()
_IllegalOperation = only IllegalOperation

_PermissionDenied :: Prism' IOErrorType ()
_PermissionDenied = only PermissionDenied

_UserError :: Prism' IOErrorType ()
_UserError = only UserError

_UnsatisfiedConstraints :: Prism' IOErrorType ()
_UnsatisfiedConstraints = only UnsatisfiedConstraints

_SystemError :: Prism' IOErrorType ()
_SystemError = only SystemError

_ProtocolError :: Prism' IOErrorType ()
_ProtocolError = only ProtocolError

_OtherError :: Prism' IOErrorType ()
_OtherError = only OtherError

_InvalidArgument :: Prism' IOErrorType ()
_InvalidArgument = only InvalidArgument

_InappropriateType :: Prism' IOErrorType ()
_InappropriateType = only InappropriateType

_HardwareFault :: Prism' IOErrorType ()
_HardwareFault = only HardwareFault

_UnsupportedOperation :: Prism' IOErrorType ()
_UnsupportedOperation = only UnsupportedOperation

_TimeExpired :: Prism' IOErrorType ()
_TimeExpired = only TimeExpired

_ResourceVanished :: Prism' IOErrorType ()
_ResourceVanished = only ResourceVanished

_Interrupted :: Prism' IOErrorType ()
_Interrupted = only Interrupted

----------------------------------------------------------------------------------------------------
-- Async Exceptions
----------------------------------------------------------------------------------------------------

-- | The current thread's stack exceeded its limit. Since an 'Exception' has
-- been raised, the thread's stack will certainly be below its limit again,
-- but the programmer should take remedial action immediately.
--
_StackOverflow :: Prism' AsyncException ()
_StackOverflow = dimap seta (either id id) . right' . rmap (const Ex.StackOverflow)
  where seta Ex.StackOverflow = Right ()
        seta t = Left t

-- | The program's heap usage has exceeded its limit.
--
-- See 'GHC.IO.Exception' for more information.
-- 
_HeapOverflow :: Prism' AsyncException ()
_HeapOverflow = dimap seta (either id id) . right' . rmap (const Ex.HeapOverflow)
  where seta Ex.HeapOverflow = Right ()
        seta t = Left t

-- | This 'Exception' is raised by another thread calling
-- 'Control.Concurrent.killThread', or by the system if it needs to terminate
-- the thread for some reason.
--
_ThreadKilled :: Prism' AsyncException ()
_ThreadKilled = dimap seta (either id id) . right' . rmap (const Ex.ThreadKilled)
  where seta Ex.ThreadKilled = Right ()
        seta t = Left t

-- | This 'Exception' is raised by default in the main thread of the program when
-- the user requests to terminate the program via the usual mechanism(s)
-- (/e.g./ Control-C in the console).
--
_UserInterrupt :: Prism' AsyncException ()
_UserInterrupt = dimap seta (either id id) . right' . rmap (const Ex.UserInterrupt)
  where seta Ex.UserInterrupt = Right ()
        seta t = Left t

----------------------------------------------------------------------------------------------------
-- Arithmetic exceptions
----------------------------------------------------------------------------------------------------

-- | Detect arithmetic overflow.
--
_Overflow :: Prism' ArithException ()
_Overflow = dimap seta (either id id) . right' . rmap (const Ex.Overflow)
  where seta Ex.Overflow = Right ()
        seta t = Left t

-- | Detect arithmetic underflow.
--
_Underflow :: Prism' ArithException ()
_Underflow = dimap seta (either id id) . right' . rmap (const Ex.Underflow)
  where seta Ex.Underflow = Right ()
        seta t = Left t

-- | Detect arithmetic loss of precision.
--
_LossOfPrecision :: Prism' ArithException ()
_LossOfPrecision = dimap seta (either id id) . right' . rmap (const Ex.LossOfPrecision)
  where seta Ex.LossOfPrecision = Right ()
        seta t = Left t

-- | Detect division by zero.
--
_DivideByZero :: Prism' ArithException ()
_DivideByZero = dimap seta (either id id) . right' . rmap (const Ex.DivideByZero)
  where seta Ex.DivideByZero = Right ()
        seta t = Left t

-- | Detect exceptional denormalized floating pure.
--
_Denormal :: Prism' ArithException ()
_Denormal = dimap seta (either id id) . right' . rmap (const Ex.Denormal)
  where seta Ex.Denormal = Right ()
        seta t = Left t

-- | Detect zero denominators.
--
-- Added in @base@ 4.6 in response to this libraries discussion:
--
-- <http://haskell.1045720.n5.nabble.com/Data-Ratio-and-exceptions-td5711246.html>
--
_RatioZeroDenominator :: Prism' ArithException ()
_RatioZeroDenominator = dimap seta (either id id) . right' . rmap (const Ex.RatioZeroDenominator)
  where seta Ex.RatioZeroDenominator = Right ()
        seta t = Left t

----------------------------------------------------------------------------------------------------
-- Array Exceptions
----------------------------------------------------------------------------------------------------

-- | Detect attempts to index an array outside its declared bounds.
--
_IndexOutOfBounds :: Prism' ArrayException String
_IndexOutOfBounds = dimap seta (either id id) . right' . rmap Ex.IndexOutOfBounds
  where seta (Ex.IndexOutOfBounds r) = Right r
        seta t = Left t

-- | Detect attempts to evaluate an element of an array that has not been initialized.
--
_UndefinedElement :: Prism' ArrayException String
_UndefinedElement = dimap seta (either id id) . right' . rmap Ex.UndefinedElement
  where seta (Ex.UndefinedElement r) = Right r
        seta t = Left t

----------------------------------------------------------------------------------------------------
-- Miscellaneous Exceptions
----------------------------------------------------------------------------------------------------

trivial :: Profunctor p => t -> Optic' p t ()
trivial t = const () `dimap` const t

_AssertionFailed :: Prism' Ex.AssertionFailed String
_AssertionFailed = iso (\(Ex.AssertionFailed a) -> a) Ex.AssertionFailed

-- | Thrown when the runtime system detects that the computation is guaranteed
-- not to terminate. Note that there is no guarantee that the runtime system
-- will notice whether any given computation is guaranteed to terminate or not.
--
_NonTermination :: Prism' Ex.NonTermination ()
_NonTermination = trivial Ex.NonTermination

-- | Thrown when the program attempts to call atomically, from the
-- 'Control.Monad.STM' package, inside another call to atomically.
--
_NestedAtomically :: Prism' Ex.NestedAtomically ()
_NestedAtomically = trivial Ex.NestedAtomically

-- | The thread is blocked on an 'Control.Concurrent.MVar.MVar', but there
-- are no other references to the 'Control.Concurrent.MVar.MVar' so it can't
-- ever continue.
--
_BlockedIndefinitelyOnMVar :: Prism' Ex.BlockedIndefinitelyOnMVar ()
_BlockedIndefinitelyOnMVar = trivial Ex.BlockedIndefinitelyOnMVar

-- | The thread is waiting to retry an 'Control.Monad.STM.STM' transaction,
-- but there are no other references to any TVars involved, so it can't ever
-- continue.
--
_BlockedIndefinitelyOnSTM :: Prism' Ex.BlockedIndefinitelyOnSTM ()
_BlockedIndefinitelyOnSTM = trivial Ex.BlockedIndefinitelyOnSTM

-- | There are no runnable threads, so the program is deadlocked. The
-- 'Deadlock' 'Exception' is raised in the main thread only.
--
_Deadlock :: Prism' Ex.Deadlock ()
_Deadlock = trivial Ex.Deadlock

-- | A class method without a definition (neither a default definition,
-- nor a definition in the appropriate instance) was called.
--
_NoMethodError :: Prism' Ex.NoMethodError String
_NoMethodError = iso (\(Ex.NoMethodError a) -> a) Ex.NoMethodError

-- | A pattern match failed.
--
_PatternMatchFail :: Prism' Ex.PatternMatchFail String
_PatternMatchFail = iso (\(Ex.PatternMatchFail a) -> a) Ex.PatternMatchFail

-- | An uninitialised record field was used.
--
_RecConError :: Prism' Ex.RecConError String
_RecConError = iso (\(Ex.RecConError a) -> a) Ex.RecConError

-- | A record selector was applied to a constructor without the appropriate
-- field. This can only happen with a datatype with multiple constructors,
-- where some fields are in one constructor but not another.
--
_RecSelError :: Prism' Ex.RecSelError String
_RecSelError = iso (\(Ex.RecSelError a) -> a) Ex.RecSelError

-- | A record update was performed on a constructor without the
-- appropriate field. This can only happen with a datatype with multiple
-- constructors, where some fields are in one constructor but not another.
--
_RecUpdError :: Prism' Ex.RecUpdError String
_RecUpdError = iso (\(Ex.RecUpdError a) -> a) Ex.RecUpdError

-- | Thrown when the user calls 'Prelude.error'.
--
_ErrorCall :: Prism' Ex.ErrorCall String
_ErrorCall = iso (\(Ex.ErrorCall a) -> a) Ex.ErrorCall

-- | This thread has exceeded its allocation limit.
--
_AllocationLimitExceeded :: Prism' Ex.AllocationLimitExceeded ()
_AllocationLimitExceeded = trivial AllocationLimitExceeded

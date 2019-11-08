module Data.Profunctor.Optic.Prism where

import Control.Exception
import Control.Monad (guard)
import Data.Bifunctor
import Data.Bits (Bits, bit, testBit)
import Data.List (stripPrefix)
import Data.Profunctor.Choice (PastroSum(..), TambaraSum(..))
import Data.Profunctor.Optic.Iso
import Data.Profunctor.Optic.Prelude 
import Data.Profunctor.Optic.Type
import GHC.IO.Exception
import qualified Control.Exception as Ex 

---------------------------------------------------------------------
-- 'Prism'
---------------------------------------------------------------------

-- | Build a 'Choice' optic from a constructor and a matcher function.
--
-- \( \quad \mathsf{Prism}\;S\;A = \exists D, S \cong D + A \)
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input functions satisfy the following
-- properties:
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
prism seta bt = dimap seta (id ||| bt) . right'

-- | Create a 'Prism' from a reviewer and a matcher function that produces a 'Maybe'.
--
prism' :: (s -> Maybe a) -> (a -> s) -> Prism' s a
prism' sma as = flip prism as $ \s -> maybe (Left s) Right (sma s)

-- | Build a 'Prism' from its free tensor representation.
--
-- Useful for constructing prisms from try and handle functions.
--
handling :: (s -> e + a) -> (e + b -> t) -> Prism s t a b
handling sea ebt = dimap sea ebt . right'

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

-- | Lift a 'Prism' into a 'PastroSum'.
--
pastroSum :: Prism s t a b -> p a b -> PastroSum p s t
pastroSum o p = withPrism o $ \sta bt -> PastroSum (join . first bt) p (swp' . sta)

-- | TODO: Document
--
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

-- | TODO: Document
--
withPrism :: APrism s t a b -> ((s -> t + a) -> (b -> t) -> r) -> r
withPrism o f = case o (PrismRep Right id) of PrismRep g h -> f g h

-- | Analogous to @(+++)@ from 'Control.Arrow'
--
splitting :: Prism s1 t1 a1 b1 -> Prism s2 t2 a2 b2 -> Prism (s1 + s2) (t1 + t2) (a1 + a2) (b1 + b2) 
splitting = split

-- | TODO: Document
--
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
-- giving a 'Prism' that matches only if all the elements of the container
-- match the 'Prism'.
--
-- >>> [Left 1, Right "foo", Left 4, Right "woot"] ^.. below right
-- []
--
-- >>> [Right "hail hydra!", Right "foo", Right "blah", Right "woot"] ^.. below right
-- [["hail hydra!","foo","blah","woot"]]
--
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
left :: Prism (a + c) (b + c) a b
left = left'

-- | TODO: Document
--
right :: Prism (c + a) (c + b) a b
right = right'

-- | Prism for the `Just` constructor of `Maybe`.
--
just :: Prism (Maybe a) (Maybe b) a b
just = flip prism Just $ maybe (Left Nothing) Right

-- | Prism for the `Nothing` constructor of `Maybe`.
--
nothing :: Prism (Maybe a) (Maybe b) () ()
nothing = flip prism  (const Nothing) $ maybe (Right ()) (const $ Left Nothing)

-- | TODO: Document
--
lowerl :: Iso s t (a + c) (b + c) -> Prism s t a b
lowerl = (. left)

-- | TODO: Document
--
lowerr :: Iso s t (c + a) (c + b) -> Prism s t a b
lowerr = (. right)

-- | Obtain a 'Prism' that can be composed with to filter another 'Lens', 'Iso', 'View', 'Fold' (or 'Traversal').
--
-- >>> [1..10] ^.. folded . filtered even
-- [2,4,6,8,10]
--
filtered :: (a -> Bool) -> Prism' a a
filtered f = iso (branch' f) join . right 

-- | TODO: Document
--
selected :: Eq a => a -> Prism' (a , b) b
selected x = flip prism ((,) x) $ \kv@(k,v) -> branch (==x) kv v k

-- | 'Prism' into the remainder of a list with a given prefix.
--
prefixed :: Eq a => [a] -> Prism' [a] [a]
prefixed ps = prism' (stripPrefix ps) (ps ++)

-- | Focus not just on a case, but a specific value of that case.
--
only :: Eq a => a -> Prism' a ()
only x = nearly x (x==)

-- | Create a 'Prism' from a value and a predicate.
--
nearly ::  a -> (a -> Bool) -> Prism' a ()
nearly x f = prism' (guard . f) (const x)

-- | Focus on the truth value of the nth bit in a bit array.
--
nthBit :: Bits s => Int -> Prism' s ()
nthBit n = prism' (guard . (flip testBit n)) (const $ bit n)

-- | TODO: Document
--
lessThan :: Bounded a => Ord a => a -> Prism' a Ordering
lessThan x = flip prism' (const x) $ \x' -> if x' < x then Just LT else Nothing  

-- | TODO: Document
--
exception :: Exception a => Prism' SomeException a
exception = prism' fromException toException

-- | Exceptions that occur in the 'IO' 'Monad'. 
--
-- An 'IOException' records a more specific error type, a descriptive string and possibly the handle 
-- that was used when the error was flagged.
--
ioException :: Prism' SomeException IOException
ioException = exception

----------------------------------------------------------------------------------------------------
-- IO Error Types
----------------------------------------------------------------------------------------------------

-- | TODO: Document
--
alreadyExists :: Prism' IOErrorType ()
alreadyExists = only AlreadyExists

-- | TODO: Document
--
noSuchThing :: Prism' IOErrorType ()
noSuchThing = only NoSuchThing

-- | TODO: Document
--
resourceBusy :: Prism' IOErrorType ()
resourceBusy = only ResourceBusy

-- | TODO: Document
--
resourceExhausted :: Prism' IOErrorType ()
resourceExhausted = only ResourceExhausted

-- | TODO: Document
--
eof :: Prism' IOErrorType ()
eof = only EOF

-- | TODO: Document
--
illegalOperation :: Prism' IOErrorType ()
illegalOperation = only IllegalOperation

-- | TODO: Document
--
permissionDenied :: Prism' IOErrorType ()
permissionDenied = only PermissionDenied

-- | TODO: Document
--
userError :: Prism' IOErrorType ()
userError = only UserError

-- | TODO: Document
--
unsatisfiedConstraints :: Prism' IOErrorType ()
unsatisfiedConstraints = only UnsatisfiedConstraints

-- | TODO: Document
--
systemError :: Prism' IOErrorType ()
systemError = only SystemError

-- | TODO: Document
--
protocolError :: Prism' IOErrorType ()
protocolError = only ProtocolError

-- | TODO: Document
--
otherError :: Prism' IOErrorType ()
otherError = only OtherError

-- | TODO: Document
--
invalidArgument :: Prism' IOErrorType ()
invalidArgument = only InvalidArgument

-- | TODO: Document
--
inappropriateType :: Prism' IOErrorType ()
inappropriateType = only InappropriateType

-- | TODO: Document
--
hardwareFault :: Prism' IOErrorType ()
hardwareFault = only HardwareFault

-- | TODO: Document
--
unsupportedOperation :: Prism' IOErrorType ()
unsupportedOperation = only UnsupportedOperation

-- | TODO: Document
--
timeExpired :: Prism' IOErrorType ()
timeExpired = only TimeExpired

-- | TODO: Document
--
resourceVanished :: Prism' IOErrorType ()
resourceVanished = only ResourceVanished

-- | TODO: Document
--
interrupted :: Prism' IOErrorType ()
interrupted = only Interrupted

----------------------------------------------------------------------------------------------------
-- Async Exceptions
----------------------------------------------------------------------------------------------------

-- | The current thread's stack exceeded its limit. Since an 'Exception' has
-- been raised, the thread's stack will certainly be below its limit again,
-- but the programmer should take remedial action immediately.
--
stackOverflow :: Prism' AsyncException ()
stackOverflow = dimap seta (either id id) . right' . rmap (const Ex.StackOverflow)
  where seta Ex.StackOverflow = Right ()
        seta t = Left t

-- | The program's heap usage has exceeded its limit.
--
-- See 'GHC.IO.Exception' for more information.
-- 
heapOverflow :: Prism' AsyncException ()
heapOverflow = dimap seta (either id id) . right' . rmap (const Ex.HeapOverflow)
  where seta Ex.HeapOverflow = Right ()
        seta t = Left t

-- | This 'Exception' is raised by another thread calling
-- 'Control.Concurrent.killThread', or by the system if it needs to terminate
-- the thread for some reason.
--
threadKilled :: Prism' AsyncException ()
threadKilled = dimap seta (either id id) . right' . rmap (const Ex.ThreadKilled)
  where seta Ex.ThreadKilled = Right ()
        seta t = Left t

-- | This 'Exception' is raised by default in the main thread of the program when
-- the user requests to terminate the program via the usual mechanism(s)
-- (/e.g./ Control-C in the console).
--
userInterrupt :: Prism' AsyncException ()
userInterrupt = dimap seta (either id id) . right' . rmap (const Ex.UserInterrupt)
  where seta Ex.UserInterrupt = Right ()
        seta t = Left t

----------------------------------------------------------------------------------------------------
-- Arithmetic exceptions
----------------------------------------------------------------------------------------------------

-- | Detect arithmetic overflow.
--
overflow :: Prism' ArithException ()
overflow = dimap seta (either id id) . right' . rmap (const Ex.Overflow)
  where seta Ex.Overflow = Right ()
        seta t = Left t

-- | Detect arithmetic underflow.
--
underflow :: Prism' ArithException ()
underflow = dimap seta (either id id) . right' . rmap (const Ex.Underflow)
  where seta Ex.Underflow = Right ()
        seta t = Left t

-- | Detect arithmetic loss of precision.
--
leftossOfPrecision :: Prism' ArithException ()
leftossOfPrecision = dimap seta (either id id) . right' . rmap (const Ex.LossOfPrecision)
  where seta Ex.LossOfPrecision = Right ()
        seta t = Left t

-- | Detect division by zero.
--
divideByZero :: Prism' ArithException ()
divideByZero = dimap seta (either id id) . right' . rmap (const Ex.DivideByZero)
  where seta Ex.DivideByZero = Right ()
        seta t = Left t

-- | Detect exceptional denormalized floating pure.
--
denormal :: Prism' ArithException ()
denormal = dimap seta (either id id) . right' . rmap (const Ex.Denormal)
  where seta Ex.Denormal = Right ()
        seta t = Left t

-- | Detect zero denominators.
--
-- Added in @base@ 4.6 in response to this libraries discussion:
--
-- <http://haskell.1045720.n5.nabble.com/Data-Ratio-and-exceptions-td5711246.html>
--
rightatioZeroDenominator :: Prism' ArithException ()
rightatioZeroDenominator = dimap seta (either id id) . right' . rmap (const Ex.RatioZeroDenominator)
  where seta Ex.RatioZeroDenominator = Right ()
        seta t = Left t

----------------------------------------------------------------------------------------------------
-- Array Exceptions
----------------------------------------------------------------------------------------------------

-- | Detect attempts to index an array outside its declared bounds.
--
indexOutOfBounds :: Prism' ArrayException String
indexOutOfBounds = dimap seta (either id id) . right' . rmap Ex.IndexOutOfBounds
  where seta (Ex.IndexOutOfBounds r) = Right r
        seta t = Left t

-- | Detect attempts to evaluate an element of an array that has not been initialized.
--
undefinedElement :: Prism' ArrayException String
undefinedElement = dimap seta (either id id) . right' . rmap Ex.UndefinedElement
  where seta (Ex.UndefinedElement r) = Right r
        seta t = Left t

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
rightecConError :: Prism' Ex.RecConError String
rightecConError = iso (\(Ex.RecConError a) -> a) Ex.RecConError

-- | A record selector was applied to a constructor without the appropriate
-- field. This can only happen with a datatype with multiple constructors,
-- where some fields are in one constructor but not another.
--
rightecSelError :: Prism' Ex.RecSelError String
rightecSelError = iso (\(Ex.RecSelError a) -> a) Ex.RecSelError

-- | A record update was performed on a constructor without the
-- appropriate field. This can only happen with a datatype with multiple
-- constructors, where some fields are in one constructor but not another.
--
rightecUpdError :: Prism' Ex.RecUpdError String
rightecUpdError = iso (\(Ex.RecUpdError a) -> a) Ex.RecUpdError

-- | Thrown when the user calls 'Prelude.error'.
--
errorCall :: Prism' Ex.ErrorCall String
errorCall = iso (\(Ex.ErrorCall a) -> a) Ex.ErrorCall

-- | This thread has exceeded its allocation limit.
--
allocationLimitExceeded :: Prism' Ex.AllocationLimitExceeded ()
allocationLimitExceeded = trivial AllocationLimitExceeded

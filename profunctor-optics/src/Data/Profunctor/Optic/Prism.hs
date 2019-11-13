module Data.Profunctor.Optic.Prism where

import Control.Exception
import Control.Monad (guard)
import Data.Bifunctor
import Data.Bits (Bits, bit, testBit)
import Data.List (stripPrefix)
import Data.Prd
import Data.Profunctor.Choice (PastroSum(..), CopastroSum(..), TambaraSum(..))
import Data.Profunctor.Optic.Iso
import Data.Profunctor.Optic.Prelude 
import Data.Profunctor.Optic.Type
import GHC.IO.Exception
import qualified Control.Exception as Ex 

---------------------------------------------------------------------
-- 'Prism'
---------------------------------------------------------------------

-- | Build a 'Prism' from a constructor and a matcher function.
--
-- \( \quad \mathsf{Prism}\;S\;A = \exists D, S \cong D + A \)
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input functions satisfy the following
-- properties:
--
-- * @sta (bt b) ≡ Right b@
--
-- * @(id ||| bt) (sta s) ≡ s@
--
-- * @left sta (sta s) ≡ left Left (sta s)@
--
-- More generally, a profunctor optic must be monoidal as a natural 
-- transformation:
-- 
-- * @o id ≡ id@
--
-- * @o ('Data.Profunctor.Composition.Procompose' p q) ≡ 'Data.Profunctor.Composition.Procompose' (o p) (o q)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
prism :: (s -> t + a) -> (b -> t) -> Prism s t a b
prism sta bt = dimap sta (id ||| bt) . right'

-- | Create a 'Prism' from a reviewer and a matcher function that produces a 'Maybe'.
--
prism' :: (s -> Maybe a) -> (a -> s) -> Prism' s a
prism' sa as = flip prism as $ \s -> maybe (Left s) Right (sa s)

-- | Build a 'Cochoice' optic from a constructor and a matcher function.
--
-- @
-- reprism f g ≡ \f g -> re (prism f g)
-- view . re $ prism bat _ ≡ bat
-- matchOf . re . re $ prism _ sa ≡ sa
-- @
--
-- A 'Reprism' is a 'View', so you can specialise types to obtain:
--
-- @ view :: 'Reprism'' s a -> s -> a @
--
reprism :: (s -> a) -> (b -> a + t) -> Reprism s t a b
reprism sa bat = unright . dimap (id ||| sa) bat

-- | Build a 'Prism' from its free tensor representation.
--
-- Useful for constructing prisms from try and handle functions.
--
handling :: (s -> c + a) -> (c + b -> t) -> Prism s t a b
handling sca cbt = dimap sca cbt . right'

-- | Build a 'Reprism' from its free tensor representation.
--
rehandling :: (c + s -> a) -> (b -> c + t) -> Reprism s t a b
rehandling csa bct = unright . dimap csa bct

-- | Lift a 'Prism' into a 'PastroSum'.
--
toPastroSum :: APrism s t a b -> p a b -> PastroSum p s t
toPastroSum o p = withPrism o $ \sta bt -> PastroSum (join . first bt) p (eswp . sta)

-- | Lift a 'Reprism' into a 'PastroSum'.
--
-- @
-- rePastroSum (re o) ≡ toPastroSum o
-- @
--
rePastroSum :: AReprism t s b a -> p s t -> PastroSum p a b
rePastroSum o p = withReprism o $ \sa bat -> PastroSum (join . first sa) p (eswp . bat)

-- | Lift a 'Prism' into a 'TambaraSum'.
--
toTambaraSum :: Choice p => APrism s t a b -> p a b -> TambaraSum p s t
toTambaraSum o p = withPrism o $ \sta bt -> TambaraSum (left . prism sta bt $ p)

-- | Lift a 'Reprism' into a 'TambaraSum'.
--
-- @
-- reTambaraSum (re o) ≡ toTambaraSum o
-- @
--
reTambaraSum :: Choice p => AReprism t s b a -> p s t -> TambaraSum p a b
reTambaraSum o p = withReprism o $ \sa bat -> TambaraSum (left . prism bat sa $ p)

-- | TODO: Document
--
clonePrism :: APrism s t a b -> Prism s t a b
clonePrism o = withPrism o prism

-- | TODO: Document
--
cloneReprism :: AReprism s t a b -> Reprism s t a b
cloneReprism o = withReprism o reprism

---------------------------------------------------------------------
-- 'PrismRep' & 'ReprismRep'
---------------------------------------------------------------------

type APrism s t a b = Optic (PrismRep a b) s t a b

type APrism' s a = APrism s s a a

-- | The 'PrismRep' profunctor precisely characterizes a 'Prism'.
--
data PrismRep a b s t = PrismRep (s -> t + a) (b -> t)

instance Functor (PrismRep a b s) where
  fmap f (PrismRep sta bt) = PrismRep (first f . sta) (f . bt)
  {-# INLINE fmap #-}

instance Profunctor (PrismRep a b) where
  dimap f g (PrismRep sta bt) = PrismRep (first g . sta . f) (g . bt)
  {-# INLINE dimap #-}

  lmap f (PrismRep sta bt) = PrismRep (sta . f) bt
  {-# INLINE lmap #-}

  rmap = fmap
  {-# INLINE rmap #-}

instance Choice (PrismRep a b) where
  left' (PrismRep sta bt) = PrismRep (either (first Left . sta) (Left . Right)) (Left . bt)
  {-# INLINE left' #-}

  right' (PrismRep sta bt) = PrismRep (either (Left . Left) (first Right . sta)) (Right . bt)
  {-# INLINE right' #-}

type AReprism s t a b = Optic (ReprismRep a b) s t a b

type AReprism' s a = AReprism s s a a

data ReprismRep a b s t = ReprismRep (s -> a) (b -> a + t) 

instance Functor (ReprismRep a b s) where
  fmap f (ReprismRep sa bat) = ReprismRep sa (second f . bat)
  {-# INLINE fmap #-}

instance Profunctor (ReprismRep a b) where
  lmap f (ReprismRep sa bat) = ReprismRep (sa . f) bat
  {-# INLINE lmap #-}

  rmap = fmap
  {-# INLINE rmap #-}

instance Cochoice (ReprismRep a b) where
  unleft (ReprismRep sca batc) = ReprismRep (sca . Left) (forgetr $ either (eassocl . batc) Right)
  {-# INLINE unleft #-}

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | Extract the two functions that characterize a 'Prism'.
--
withPrism :: APrism s t a b -> ((s -> t + a) -> (b -> t) -> r) -> r
withPrism o f = case o (PrismRep Right id) of PrismRep g h -> f g h

-- | Extract the two functions that characterize a 'Reprism'.
--
withReprism :: AReprism s t a b -> ((s -> a) -> (b -> a + t) -> r) -> r
withReprism o f = case o (ReprismRep id Right) of ReprismRep g h -> f g h

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
  withPrism k $ \sta bt ->
    flip prism (fmap bt) $ \(e,s) ->
      case sta s of
        Left t  -> Left  (e,t)
        Right a -> Right (e,a)
{-# INLINE aside #-}

-- | Given a pair of prisms, project sums.
without :: APrism s t a b -> APrism u v c d -> Prism (s + u) (t + v) (a + c) (b + d)
without k =
  withPrism k $ \sta bt k' ->
    withPrism k' $ \uevc dv ->
      flip prism (bimap bt dv) $ \su ->
        case su of
          Left s  -> bimap Left Left (sta s)
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
  withPrism k $ \sta bt ->
    flip prism (fmap bt) $ \s ->
      case traverse sta s of
        Left _  -> Left s
        Right t -> Right t
{-# INLINE below #-}

---------------------------------------------------------------------
-- Common 'Prism's and 'Reprism's
---------------------------------------------------------------------

-- | 'Prism' into the `Left` constructor of `Either`.
--
left :: Prism (a + c) (b + c) a b
left = left'

-- | 'Prism' into the `Right` constructor of `Either`.
--
right :: Prism (c + a) (c + b) a b
right = right'

-- | 'Reprism' out of the `Left` constructor of `Either`.
--
releft :: Reprism a b (a + c) (b + c)
releft = unleft

-- | 'Reprism' out of the `Right` constructor of `Either`.
--
reright :: Reprism a b (c + a) (c + b)
reright = unright

-- | 'Prism' into the `Just` constructor of `Maybe`.
--
just :: Prism (Maybe a) (Maybe b) a b
just = flip prism Just $ maybe (Left Nothing) Right

-- | 'Prism' into the `Nothing` constructor of `Maybe`.
--
nothing :: Prism (Maybe a) (Maybe b) () ()
nothing = flip prism  (const Nothing) $ maybe (Right ()) (const $ Left Nothing)

-- | Match a given key to obtain the associated value. 
--
keyed :: Eq a => a -> Prism' (a , b) b
keyed x = flip prism ((,) x) $ \kv@(k,v) -> branch (==x) kv v k

-- | Filter another optic.
--
-- >>> [1..10] ^.. folded id . filtered even
-- [2,4,6,8,10]
--
filtered :: (a -> Bool) -> Prism' a a
filtered f = iso (branch' f) join . right 

-- | Focus on comparability to a given element of a partial order.
--
compared :: Eq a => Prd a => a -> Prism' a Ordering
compared x = flip prism' (const x) (pcompare x)

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
nthbit :: Bits s => Int -> Prism' s ()
nthbit n = prism' (guard . (flip testBit n)) (const $ bit n)

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
leftossOfPrecision :: Prism' ArithException ()
leftossOfPrecision = dimap sta (either id id) . right' . rmap (const Ex.LossOfPrecision)
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
rightatioZeroDenominator :: Prism' ArithException ()
rightatioZeroDenominator = dimap sta (either id id) . right' . rmap (const Ex.RatioZeroDenominator)
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

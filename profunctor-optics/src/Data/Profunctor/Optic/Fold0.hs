module Data.Profunctor.Optic.Fold0 where

import Control.Exception (Exception(..), SomeException, AsyncException, ArrayException, ArithException)
import Control.Monad ((<=<))
import Control.Monad (liftM)
import Control.Monad.Reader as Reader
import Control.Monad.State as State
import Data.Foldable (traverse_)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe
import Data.Profunctor.Optic.Prelude
import Data.Profunctor.Optic.Prism
import Data.Profunctor.Optic.Prism (_Just)
import Data.Profunctor.Optic.Setter
import Data.Profunctor.Optic.Traversal0
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.View (view, to)
import Data.Semigroup
import Foreign.C.Types
import GHC.Conc (ThreadId)
import GHC.IO.Exception
import System.IO
import UnliftIO (MonadUnliftIO)

import qualified Control.Exception as Ex 
import qualified Data.List.NonEmpty as NE
import qualified UnliftIO.Exception as Ux


---------------------------------------------------------------------
-- 'Fold0'
---------------------------------------------------------------------

-- | Build a 'Fold0' from an arbitrary function.
--
-- >>> [Just 1, Nothing] ^.. folding id . fold0 id
-- [1]
--
-- @
-- 'fold0' ('toMaybeOf' o) ≡ o
-- 'fold0' ('view' o) ≡ o . '_Just'
-- @
--
fold0 :: (s -> Maybe a) -> Fold0 s a
fold0 f = to (\s -> maybe (Left s) Right (f s)) . pright

infixl 3 `failing` -- Same as (<|>)

-- | Try the first 'Fold0'. If it returns no entry, try the second one.
--
-- >>> preview (ix 1 . re _L `failing` ix 2 . re _R) [0,1,2,3]
-- Just (Left 1)
--
-- >>> preview (ix 42 . re _L `failing` ix 2 . re _R) [0,1,2,3]
-- Just (Right 2)
--
failing :: AFold0 a s a -> AFold0 a s a -> Fold0 s a
failing a b = fold0 $ \s -> maybe (preview b s) Just (preview a s)
{-# INLINE failing #-}

-- | TODO: Document
--
toView :: Monoid a => AFold0 a s a -> View s (Maybe a)
toView = to . preview

-- | Build a 'Fold0' from a 'View'.
--
-- @
-- 'fromView' o ≡ o . '_Just'
-- 'fromView' o ≡ 'fold0' ('view' o)
-- @
--
fromView :: View s (Maybe a) -> Fold0 s a
fromView = (. _Just)

---------------------------------------------------------------------
-- 'Fold0Rep'
---------------------------------------------------------------------

newtype Fold0Rep r a b = Fold0Rep { runFold0Rep :: a -> Maybe r }

type AFold0 r s a = Optic' (Fold0Rep r) s a

instance Functor (Fold0Rep r a) where
  fmap _ (Fold0Rep p) = Fold0Rep p

instance Contravariant (Fold0Rep r a) where
  contramap _ (Fold0Rep p) = Fold0Rep p

instance Profunctor (Fold0Rep r) where
  dimap f _ (Fold0Rep p) = Fold0Rep (p . f)

instance Choice (Fold0Rep r) where
  left' (Fold0Rep p) = Fold0Rep (either p (const Nothing))
  right' (Fold0Rep p) = Fold0Rep (either (const Nothing) p)

instance Cochoice (Fold0Rep r) where
  unleft  (Fold0Rep k) = Fold0Rep (k . Left)
  unright (Fold0Rep k) = Fold0Rep (k . Right)

instance Strong (Fold0Rep r) where
  first' (Fold0Rep p) = Fold0Rep (p . fst)
  second' (Fold0Rep p) = Fold0Rep (p . snd)

instance Sieve (Fold0Rep r) (Pre r) where
  sieve = (Pre .) . runFold0Rep

instance Representable (Fold0Rep r) where
  type Rep (Fold0Rep r) = Pre r
  tabulate = Fold0Rep . (getPre .)
  {-# INLINE tabulate #-}

-- | 'Pre' is 'Maybe' with a phantom type variable.
--
newtype Pre a b = Pre { getPre :: Maybe a } deriving (Eq, Ord, Show)

instance Functor (Pre a) where fmap f (Pre p) = Pre p

instance Contravariant (Pre a) where contramap f (Pre p) = Pre p

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

previewOf :: Optic' (Fold0Rep r) s a -> (a -> Maybe r) -> s -> Maybe r
previewOf = between runFold0Rep Fold0Rep

toMaybeOf :: AFold0 a s a -> s -> Maybe a
toMaybeOf = flip previewOf Just


---------------------------------------------------------------------
-- Derived operators
---------------------------------------------------------------------

preview :: MonadReader s m => AFold0 a s a -> m (Maybe a)
preview o = Reader.asks $ toMaybeOf o

preuse :: MonadState s m => AFold0 a s a -> m (Maybe a)
preuse o = State.gets $ preview o

infixl 8 ^?

-- | An infix variant of 'preview''.
--
-- Performs a safe 'head' of a 'Fold' or 'Traversal' or retrieve 'Just'
-- the result from a 'View' or 'Lens'.
--
-- When using a 'Traversal' as a partial 'Lens', or a 'Fold' as a partial
-- 'View' this can be a convenient way to extract the optional value.
--
--
-- >>> Left 4 ^? _L
-- Just 4
--
-- >>> Right 4 ^? _L
-- Nothing
--
-- @
-- ('^?') ≡ 'flip' 'preview''
-- @
--
-- @
-- ('^?') :: s -> 'View' s a         -> 'Maybe' a
-- ('^?') :: s -> 'Fold' s a         -> 'Maybe' a
-- ('^?') :: s -> 'Lens'' s a        -> 'Maybe' a
-- ('^?') :: s -> 'Prism'' s a       -> 'Maybe' a
-- ('^?') :: s -> 'Traversal0'' s a      -> 'Maybe' a
-- ('^?') :: s -> 'Iso'' s a         -> 'Maybe' a
-- ('^?') :: s -> 'Traversal'' s a   -> 'Maybe' a
-- @
--
(^?) :: s -> AFold0 a s a -> Maybe a
s ^? o = toMaybeOf o s

-- | Check to see if this 'Fold0' doesn't match.
--
-- >>> isnt _Just Nothing
-- True
--
isnt :: AFold0 a s a -> s -> Bool
isnt k s = not (isJust (preview k s))
{-# INLINE isnt #-}

---------------------------------------------------------------------
-- Exception handling
---------------------------------------------------------------------

-- | A variant of 'Control.Exception.try' that takes a 'Prism' (or any 'Fold') to select which
-- exceptions are catches. If the 'Exception' does not match the predicate, it is re-thrown.
--
-- Note that this will not catch asynchronous exceptions.
--
tries :: (MonadUnliftIO m, Exception s) => AFold0 a s a -> m r -> m (Either a r)
tries o = Ux.tryJust (preview o)

-- | A variant of 'tries' that returns exceptions.
--
tries' :: (MonadUnliftIO m, Exception a) => m r -> m (Either a r)
tries' = tries excepted

-- | A variant of 'tries' that discards the specific exception thrown.
--
tries_ :: (MonadUnliftIO m, Exception s) => AFold0 a s a -> m r -> m (Maybe r)
tries_ o m = preview right' `liftM` tries o m

-- | Catch exceptions that match a given 'Prism' (or any 'Fold', really).
--
-- Note that this will not catch asynchronous exceptions.
--
-- >>> catches _AssertionFailed (assert False (return "uncatches")) $ \ _ -> return "catches"
-- "catches"
--
catches :: MonadUnliftIO m => Exception s => AFold0 a s a -> m r -> (a -> m r) -> m r
catches o = Ux.catchJust (preview o)

-- | A variant of 'catches' specialized to only 'IOException's.
--
catches' :: MonadUnliftIO m => m r -> (IOException -> m r) -> m r
catches' = catches _IOException

-- | Catch exceptions that match a given 'Prism' (or any 'Getter'), discarding
-- the information about the match. This is particuarly useful when you have
-- a @'Prism'' e ()@ where the result of the 'Prism' or 'Fold' isn't
-- particularly valuable, just the fact that it matches.
--
-- >>> catches_ _AssertionFailed (assert False (return "uncatches")) $ return "catches"
-- "catches"
--
catches_ :: MonadUnliftIO m => Exception s => AFold0 a s a -> m r -> m r -> m r
catches_ o a b = Ux.catchJust (preview o) a (const b)

-- | A version of 'catches' with the arguments swapped around; useful in
-- situations where the code for the handler is shorter.
--
-- >>> handles _Overflow (\_ -> return "catches") $ throwIO Overflow
-- "catches"
--
handles :: (MonadUnliftIO m, Exception s) => AFold0 a s a -> (a -> m r) -> m r -> m r
handles o = flip (catches o)

-- | A version of 'catches_' with the arguments swapped around; useful in
-- situations where the code for the handler is shorter.
--
-- >>> handles_ _Overflow (return "catches") $ throwIO Overflow
-- "catches"
--
handles_ :: (MonadUnliftIO m, Exception s) => AFold0 a s a -> m r -> m r -> m r
handles_ o = flip (catches_ o)

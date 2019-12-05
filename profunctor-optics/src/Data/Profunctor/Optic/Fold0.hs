{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Fold0 (
    -- * Fold0 & Ixfold0
    Fold0
  , fold0
  , ixfold0
  , failing
  , toFold0
  , fromFold0 
    -- * Optics
  , folded0
  , filtered
    -- * Primitive operators
  , withFold0
  , withIxfold0
    -- * Operators
  , (^?)
  , preview 
  , preuse
    -- * Indexed operators
  , ixpreview
  , ixpreviews
    -- * MonadUnliftIO 
  , tries
  , tries_ 
  , catches
  , catches_
  , handles
  , handles_
    -- * Carriers
  , Fold0Rep(..)
  , AFold0
  , AIxfold0
  , Pre(..)
    -- * Classes
  , Strong(..)
  , Choice(..)
) where

import Control.Applicative
import Control.Exception (Exception)
import Control.Monad ((<=<), void)
import Control.Monad.IO.Unlift
import Control.Monad.Reader as Reader hiding (lift)
import Control.Monad.State as State hiding (lift)
import Data.Foldable (Foldable, foldMap, traverse_)
import Data.Maybe
import Data.Monoid hiding (All(..), Any(..))
import Data.Prd (Prd(..), Min(..), Max(..))
import Data.Prd.Lattice (Lattice(..))
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Prism (just, async)
import Data.Profunctor.Optic.Traversal0 (traversal0Vl, ixtraversal0Vl, is)
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.View (AView, to, from, withPrimView, view, cloneView)
import Data.Semiring (Semiring(..), Prod(..))
import qualified Control.Exception as Ex
import qualified Data.List.NonEmpty as NEL
import qualified Data.Prd as Prd
import qualified Data.Semiring as Rng

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> import Control.Exception hiding (catches)
-- >>> import Data.Functor.Identity
-- >>> import Data.List.Index
-- >>> import Data.List.NonEmpty (NonEmpty(..))
-- >>> import Data.Map as Map
-- >>> import Data.Maybe
-- >>> import Data.Monoid
-- >>> import Data.Semiring hiding (unital,nonunital,presemiring)
-- >>> import Data.Sequence as Seq
-- >>> import qualified Data.List.NonEmpty as NE
-- >>> :load Data.Profunctor.Optic
-- >>> let ixtraversed :: Ixtraversal Int [a] [b] a b ; ixtraversed = ixtraversalVl itraverse

---------------------------------------------------------------------
-- 'Fold0' & 'Ixfold0'
---------------------------------------------------------------------

type AFold0 r s a = Optic' (Fold0Rep r) s a

type AIxfold0 r i s a = IndexedOptic' (Fold0Rep r) i s a

-- | Obtain a 'Fold0' directly.
--
-- @
-- 'fold0' . 'preview' ≡ id
-- 'fold0' ('view' o) ≡ o . 'just'
-- @
--
-- >>> preview (fold0 . preview $ selected even) (2, "yes")
-- Just "yes"
--
-- >>> preview (fold0 . preview $ selected even) (3, "no")
-- Nothing
--
-- >>> preview (fold0 listToMaybe) "foo"
-- Just 'f'
--
fold0 :: (s -> Maybe a) -> Fold0 s a
fold0 f = to (\s -> maybe (Left s) Right (f s)) . right'
{-# INLINE fold0 #-}

-- | Create an 'Ixfold0' from a partial function.
ixfold0 :: (s -> Maybe (i, a)) -> Ixfold0 i s a
ixfold0 g = ixtraversal0Vl (\point f s -> maybe (point s) (uncurry f) $ g s) . coercer
{-# INLINE ixfold0 #-}

infixl 3 `failing` -- Same as (<|>)

-- | Try the first 'Fold0'. If it returns no entry, try the second one.
--
failing :: AFold0 a s a -> AFold0 a s a -> Fold0 s a
failing a b = fold0 $ \s -> maybe (preview b s) Just (preview a s)
{-# INLINE failing #-}

-- | Obtain a 'Fold0' from a 'View'.
--
-- @
-- 'toFold0' o ≡ o . 'just'
-- 'toFold0' o ≡ 'fold0' ('view' o)
-- @
--
toFold0 :: View s (Maybe a) -> Fold0 s a
toFold0 = (. just)
{-# INLINE toFold0 #-}

-- | Obtain a partial 'View' from a 'Fold0' 
--
fromFold0 ::  AFold0 a s a -> View s (Maybe a)
fromFold0 = to . preview
{-# INLINE fromFold0 #-}

---------------------------------------------------------------------
-- Optics 
---------------------------------------------------------------------

-- | Obtain a 'Fold0' from a partial function.
--
-- >>> [Just 1, Nothing] ^.. folded . folded0
-- [1]
--
folded0 :: Fold0 (Maybe a) a
folded0 = fold0 id
{-# INLINE folded0 #-}

-- | Filter another optic.
--
-- >>> [1..10] ^.. folded . filtered even
-- [2,4,6,8,10]
--
filtered :: (a -> Bool) -> Fold0 a a
filtered p = traversal0Vl (\point f a -> if p a then f a else point a) . coercer
{-# INLINE filtered #-}

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | TODO: Document
--
withFold0 :: Optic (Fold0Rep r) s t a b -> (a -> Maybe r) -> s -> Maybe r
withFold0 o = runFold0Rep #. o .# Fold0Rep
{-# INLINE withFold0 #-}

-- | TODO: Document
--
withIxfold0 :: AIxfold0 r i s a -> (i -> a -> Maybe r) -> i -> s -> Maybe r
withIxfold0 o f = curry $ withFold0 o (uncurry f)
{-# INLINE withIxfold0 #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

infixl 8 ^?

-- | An infix variant of 'preview''.
--
-- @
-- ('^?') ≡ 'flip' 'preview''
-- @
--
-- Perform a safe 'head' of a 'Fold' or 'Traversal' or retrieve 'Just'
-- the result from a 'View' or 'Lens'.
--
-- When using a 'Traversal' as a partial 'Lens', or a 'Fold' as a partial
-- 'View' this can be a convenient way to extract the optional value.
--
-- >>> Left 4 ^? left
-- Just 4
--
-- >>> Right 4 ^? left
-- Nothing
--
(^?) :: s -> AFold0 a s a -> Maybe a
(^?) = flip preview
{-# INLINE (^?) #-}

-- | TODO: Document
--
preview :: MonadReader s m => AFold0 a s a -> m (Maybe a)
preview o = Reader.asks $ withFold0 o Just
{-# INLINE preview #-}

-- | TODO: Document
--
preuse :: MonadState s m => AFold0 a s a -> m (Maybe a)
preuse o = State.gets $ preview o
{-# INLINE preuse #-}

------------------------------------------------------------------------------
-- Indexed operators
------------------------------------------------------------------------------

-- | TODO: Document 
--
ixpreview :: Monoid i => AIxfold0 (i , a) i s a -> s -> Maybe (i , a)
ixpreview o = ixpreviews o (,)
{-# INLINE ixpreview #-}

-- | TODO: Document 
--
ixpreviews :: Monoid i => AIxfold0 r i s a -> (i -> a -> r) -> s -> Maybe r
ixpreviews o f = withIxfold0 o (\i -> Just . f i) mempty
{-# INLINE ixpreviews #-}

------------------------------------------------------------------------------
-- 'MonadUnliftIO'
------------------------------------------------------------------------------

-- | Test for synchronous exceptions that match a given optic.
--
-- In the style of 'safe-exceptions' this function rethrows async exceptions 
-- synchronously in order to preserve async behavior,
-- 
-- @
-- 'tries' :: 'MonadUnliftIO' m => 'AFold0' e 'Ex.SomeException' e -> m a -> m ('Either' e a)
-- 'tries' 'exception' :: 'MonadUnliftIO' m => 'Exception' e => m a -> m ('Either' e a)
-- @
--
tries :: MonadUnliftIO m => Exception ex => AFold0 e ex e -> m a -> m (Either e a)
tries o a = withRunInIO $ \run -> run (Right `liftM` a) `Ex.catch` \e ->
  if is async e then throwM e else run $ maybe (throwM e) (return . Left) (preview o e)
{-# INLINE tries #-}

-- | A variant of 'tries' that returns synchronous exceptions.
--
tries_ :: MonadUnliftIO m => Exception ex => AFold0 e ex e -> m a -> m (Maybe a)
tries_ o a = preview right' `liftM` tries o a
{-# INLINE tries_ #-}

-- | Catch synchronous exceptions that match a given optic.
--
-- Rethrows async exceptions synchronously in order to preserve async behavior.
--
-- @
-- 'catches' :: 'MonadUnliftIO' m => 'AFold0' e 'Ex.SomeException' e -> m a -> (e -> m a) -> m a
-- 'catches' 'exception' :: 'MonadUnliftIO' m => Exception e => m a -> (e -> m a) -> m a
-- @
--
-- >>> catches (only Overflow) (throwIO Overflow) (\_ -> return "caught")
-- "caught"
--
catches :: MonadUnliftIO m => Exception ex => AFold0 e ex e -> m a -> (e -> m a) -> m a
catches o a ea = withRunInIO $ \run -> run a `Ex.catch` \e ->
  if is async e then throwM e else run $ maybe (throwM e) ea (preview o e)
{-# INLINE catches #-}

-- | Catch synchronous exceptions that match a given optic, discarding the match.
--
-- >>> catches_ (only Overflow) (throwIO Overflow) (return "caught")
-- "caught"
--
catches_ :: MonadUnliftIO m => Exception ex => AFold0 e ex e -> m a -> m a -> m a
catches_ o x y = catches o x $ const y
{-# INLINE catches_ #-}

-- | Flipped variant of 'catches'.
--
-- >>> handles (only Overflow) (\_ -> return "caught") $ throwIO Overflow
-- "caught"
--
handles :: MonadUnliftIO m => Exception ex => AFold0 e ex e -> (e -> m a) -> m a -> m a
handles o = flip $ catches o
{-# INLINE handles #-}

-- | Flipped variant of 'catches_'.
--
-- >>> handles_ (only Overflow) (return "caught") $ throwIO Overflow
-- "caught"
--
handles_ :: MonadUnliftIO m => Exception ex => AFold0 e ex e -> m a -> m a -> m a
handles_ o = flip $ catches_ o
{-# INLINE handles_ #-}

throwM :: MonadIO m => Exception e => e -> m a
throwM = liftIO . Ex.throwIO
{-# INLINE throwM #-}

---------------------------------------------------------------------
-- 'Fold0Rep'
---------------------------------------------------------------------

newtype Fold0Rep r a b = Fold0Rep { runFold0Rep :: a -> Maybe r }

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

instance Functor (Pre a) where fmap _ (Pre p) = Pre p

instance Contravariant (Pre a) where contramap _ (Pre p) = Pre p

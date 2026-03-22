{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE FlexibleContexts      #-}
module Data.Profunctor.Optic.View (
    -- * Constructors
    View
  , to
  , like
  , cloneView
    -- *** Dual Constructors
  , Review
  , from
  , unlike
  , cloneReview
    -- * Indexed Constructors
  , ixto
  , ixlike
    -- *** Coindexed Constructors
  , cxfrom
    -- * Optics
  , tupling
    -- *** Dual Optics
  , summing
    -- * Operators
  , view
  , views
  , viewing
    -- *** Dual Operators
  , review
  , reviews
    -- * Indexed Operators
  , ixview
  , ixviews
    -- *** Coindexed Operators
  , cxreview
  , cxreviews
    -- * MonadState
  , use
  , uses
  , reuse
  , reuses
) where

import Control.Monad.Reader as Reader
import Control.Monad.State as State
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Combinator
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Fold

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> :set -XRank2Types
-- >>> import Data.Either
-- >>> import qualified Data.Map.Lazy as Map
-- >>> import Control.Monad.State
-- >>> import Control.Monad.Writer
-- >>> :load Data.Profunctor.Optic
-- >>> import Prelude
-- >>> import Data.Monoid (Sum(..))

---------------------------------------------------------------------
-- * Constructors
---------------------------------------------------------------------

-- | Obtain a 'View' from an arbitrary function.
--
-- @
-- 'to' f '.' 'to' g ≡ 'to' (g '.' f)
-- a '^.' 'to' f ≡ f a
-- @
--
-- >>> ("hello","world") ^. to snd
-- "world"
--
-- >>> 5 ^. to succ
-- 6
--
-- >>> (0, -5) ^. second' . to abs
-- 5
--
-- @
-- 'to' :: (s -> a) -> 'View' s a
-- @
--
to :: (s -> a) -> View s a
to f = coercedR . lmap f
{-# INLINE to #-}

-- | Obtain a constant-valued (index-preserving) 'View' from an arbitrary value.
--
-- This can be useful as a second case 'failing' a 'Fold'
-- e.g. @foo `failing` 'like' 0@
--
-- @
-- 'like' a '.' 'like' b ≡ 'like' b
-- a '^.' 'like' b ≡ b
-- a '^.' 'like' b ≡ a '^.' 'to' ('const' b)
-- @
--
--
-- @
-- 'like' :: a -> 'View' s a
-- @
--
like :: a -> View s a
like a = to (const a)
{-# INLINE like #-}

-- | TODO: Document
--
-- @
-- 'cloneView' :: 'Monoid' a => 'AView' a s a -> 'Fold' s a
-- @
--
cloneView :: AView a s a -> View s a
cloneView o = to (view o)
{-# INLINE cloneView #-}

---------------------------------------------------------------------
-- *** Dual Constructors
---------------------------------------------------------------------

-- | Obtain a 'Review' from an arbitrary function.
--
-- @
-- 'from' ≡ 're' . 'to'
-- @
--
-- >>> review (from Prelude.length) [1,2,3]
-- 3
--
-- @
-- 'from' :: (b -> t) -> 'Review' t b
-- @
--
from :: (b -> t) -> Review t b
from f = coercedL . rmap f
{-# INLINE from #-}

-- | Obtain a constant-valued (index-preserving) 'Review' from an arbitrary value.
--
-- @
-- 'unlike' a '.' 'unlike' b ≡ 'unlike' a
-- 'unlike' a '.^' b ≡ a
-- 'unlike' a '.^' b ≡ 'from' ('const' a) '#' b
-- @
--
unlike :: t -> Review t b
unlike t = from (const t)
{-# INLINE unlike #-}

-- | TODO: Document
--
cloneReview :: AReview t b -> Review t b
cloneReview o = from (review o)
{-# INLINE cloneReview #-}

---------------------------------------------------------------------
-- * Indexed Constructors
---------------------------------------------------------------------

-- | TODO: Document
--
-- @since 0.0.3
ixto :: (s -> (k , a)) -> Ixview k s a
ixto f = coercedR . lmap (f . snd)
{-# INLINE ixto #-}

-- | TODO: Document
--
-- @since 0.0.3
ixlike :: k -> a -> Ixview k s a
ixlike k a = ixto (const (k, a))
{-# INLINE ixlike #-}

---------------------------------------------------------------------
-- *** Coindexed Constructors
---------------------------------------------------------------------

-- | TODO: Document
--
-- >>> cxfoldMapOf (cxfrom Map.mapWithKey # cxfrom Map.mapWithKey) (\k r a -> Map.singleton k (a + r)) 1.0 $ Map.fromList [("k",Map.fromList [("l",2.0)])]
-- fromList [("k",fromList [("l",fromList [("kl",3.0)])])]
--
-- @since 0.0.3
cxfrom :: ((k -> b) -> t) -> Cxreview k t b
cxfrom f = coercedL . rmap (\ib _ -> f ib)
{-# INLINE cxfrom #-}

---------------------------------------------------------------------
-- * Optics
---------------------------------------------------------------------

-- | Combine two 'View's into a 'View' to a product.
--
-- @
-- 'tupling' :: 'View' s a1 -> 'View' s a2 -> 'View' s (a1 , a2)
-- @
--
tupling :: AView a1 s a1 -> AView a2 s a2 -> View s (a1 , a2)
tupling l r = to (fanout (view l) (view r))
{-# INLINE tupling #-}

---------------------------------------------------------------------
-- *** Dual Optics
---------------------------------------------------------------------

-- | Combine two 'Review's into a 'Review' from a sum.
--
-- @
-- 'summing' :: 'Review' t b1 -> 'Review' t b2 -> 'Review' t (b1 + b2)
-- @
--
summing :: AReview t b1 -> AReview t b2 -> Review t (b1 + b2)
summing l r = from (either (review l) (review r))
{-# INLINE summing #-}

---------------------------------------------------------------------
-- * Operators
---------------------------------------------------------------------

-- | An infix alias for 'view'.
--
-- Fiity and semantics are such that subsequent field accesses can be
-- performed with ('Prelude..').
--
-- >>> ("hello","world") ^. second'
-- "world"
--
-- | View the focus of an optic.
--
-- @
-- 'view' '.' 'to' ≡ 'id'
-- @
--
-- >>> view second' (1, "hello")
-- "hello"
--
-- >>> view (to succ) 5
-- 6
--
-- >>> view (second' . first') ("hello",("world","!!!"))
-- "world"
--
-- /Benchmark: 0.95x vs direct getter (zero-cost). See "Data.Profunctor.Optic.Bench"./
--
view :: MonadReader s m => AView a s a -> m a
view o = views o id
{-# INLINE view #-}

-- | Map each part of a structure viewed to a semantic editor combinator.
--
-- @
-- 'views o f ≡ withForget o f'
-- 'Data.Foldable.foldMap' = 'views' 'folding''
-- @
--
-- >>> views bitraversed id (["foo"], ["bar", "baz"])
-- ["foo","bar","baz"]
--
views :: MonadReader s m => AView r s a -> (a -> r) -> m r
views o f = asks $ foldMapOf o f
{-# INLINE views #-}

-- | Obtain a 'View' from an 'AFold0'.
--
-- @'viewing' ≡ 'to' '.' 'preview'@
--
viewing :: AFold0 a s a -> View s (Maybe a)
viewing o = coercedR . lmap (preview o)
{-# INLINE viewing #-}

---------------------------------------------------------------------
-- *** Dual Operators
---------------------------------------------------------------------

-- | Review the focus of an optic.
--
-- @
-- 'review' ≡ 'view' '.' 're'
-- 'review' . 'from' ≡ 'id'
-- @
--
-- >>> review left' 4
-- Left 4
--
review :: AReview t b -> b -> t
review o = reviews o id
{-# INLINE review #-}

-- | Turn an optic around and look through the other end, applying a function.
--
-- @
-- 'reviews' ≡ 'views' '.' 're'
-- 'reviews' ('from' f) g ≡ g '.' f
-- @
--
-- >>> reviews left isRight "mustard"
-- False
-- >>> reviews (from succ) (*2) 3
-- 8
--
reviews :: AReview t b -> (t -> r) -> b -> r
reviews o f = f . unTagged #. o .# Tagged
{-# INLINE reviews #-}

---------------------------------------------------------------------
-- * Indexed Operators
---------------------------------------------------------------------

-- | View the focus of an indexed optic along with its index.
--
-- >>> ixview ixfirst ("foo", 42) :: (Maybe (Sum Int), String)
-- (Just (Sum {getSum = 0}),"foo")
--
-- @since 0.0.3
ixview :: MonadReader s m => Monoid k => AIxview k s a -> m (Maybe k , a)
ixview o = ixviews o $ \k a -> (Just k, a)
{-# INLINE ixview #-}

-- | Bring a function of the index and value of an indexed optic into the current environment.
--
-- Use 'ixview' if there is a need to disambiguate between 'mempty' as a miss vs. as a return value.
--
-- @since 0.0.3
ixviews :: MonadReader s m => Monoid k => Ixoptic' (Star (Const r)) k s a -> (k -> a -> r) -> m r
ixviews o f = asks $ ixfoldMapOf o f
{-# INLINE ixviews #-}

---------------------------------------------------------------------
-- *** Coindexed Operators
---------------------------------------------------------------------

-- | Bring a function of the index of a co-indexed optic into the current environment.
--
-- @since 0.0.3
cxreview :: ACxreview k t b -> b -> (k -> t)
cxreview o = cxreviews o id
{-# INLINE cxreview #-}

-- | Bring a continuation of the index of a co-indexed optic into the current environment.
--
-- @
-- cxreviews :: ACxreview k t b -> ((k -> t) -> r) -> b -> r
-- @
--
-- @since 0.0.3
cxreviews :: ACxreview k t b -> ((k -> t) -> r) -> b -> r
cxreviews o f = unwrap o f . const where unwrap o1 f1 = f1 . unTagged #. o1 .# Tagged
{-# INLINE cxreviews #-}

---------------------------------------------------------------------
-- * MonadState
---------------------------------------------------------------------

-- | TODO: Document
--
use :: MonadState s m => AView a s a -> m a
use o = gets (view o)
{-# INLINE use #-}

-- | Use the target of an optic in the current state.
--
-- >>> evalState (uses first length) ("hello","world!")
-- 5
--
uses :: MonadState s m => AFold r s a -> (a -> r) -> m r
uses l f = gets (views l f)
{-# INLINE uses #-}

-- | Turn an optic around and 'use' a value (or the current environment) through it the other way.
--
-- @
-- 'reuse' ≡ 'use' '.' 're'
-- 'reuse' '.' 'from' ≡ 'gets'
-- @
--
-- >>> evalState (reuse left) 5
-- Left 5
-- >>> evalState (reuse (from succ)) 5
-- 6
--
reuse :: MonadState b m => AReview t b -> m t
reuse o = gets (unTagged #. o .# Tagged)
{-# INLINE reuse #-}

-- | Turn an optic around and 'use' the current state through it the other way, applying a function.
--
-- @
-- 'reuses' ≡ 'uses' '.' 're'
-- 'reuses' ('from' f) g ≡ 'gets' (g '.' f)
-- @
--
-- >>> evalState (reuses left isLeft) (5 :: Int)
-- True
--
reuses :: MonadState b m => AReview t b -> (t -> r) -> m r
reuses o tr = gets (tr . unTagged #. o .# Tagged)
{-# INLINE reuses #-}

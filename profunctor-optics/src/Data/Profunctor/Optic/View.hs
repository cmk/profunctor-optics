{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE FlexibleContexts      #-}
module Data.Profunctor.Optic.View (
    -- * View
    View
  , Review
  , to
  , ixto
  , from
  , rxfrom
  , cloneView
  , cloneReview
    -- * Optics
  , like
  , ixlike
  , relike
  , toProduct
  , fromSum
    -- * Operators
  , (^.)
  , view
  , views
  , (^%)
  , viewWithKey
  , viewsWithKey
  , (.^)
  , review
  , reviews
  , reviewWithKey
  , reviewsWithKey
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

---------------------------------------------------------------------
-- 'View' & 'Review'
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
to f = coercer . lmap f
{-# INLINE to #-}

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
from f = coercel . rmap f
{-# INLINE from #-}

-- | TODO: Document
--
-- @
-- 'cloneView' :: 'Monoid' a => 'AView' a s a -> 'Fold' s a
-- @
--
cloneView :: AView a s a -> View s a
cloneView = to . view
{-# INLINE cloneView #-}

-- | TODO: Document
--
cloneReview :: AReview t b -> Review t b
cloneReview = from . review
{-# INLINE cloneReview #-}

---------------------------------------------------------------------
-- Optics 
---------------------------------------------------------------------

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
like = to . const
{-# INLINE like #-}

-- | Obtain a constant-valued (index-preserving) 'Review' from an arbitrary value.
--
-- @
-- 'relike' a '.' 'relike' b ≡ 'relike' a
-- 'relike' a '.^' b ≡ a
-- 'relike' a '.^' b ≡ 'from' ('const' a) '#' b
-- @
--
relike :: t -> Review t b
relike = from . const
{-# INLINE relike #-}

-- | Combine two 'View's into a 'View' to a product.
--
-- @
-- 'toProduct' :: 'View' s a1 -> 'View' s a2 -> 'View' s (a1 , a2)
-- @
--
toProduct :: AView a1 s a1 -> AView a2 s a2 -> View s (a1 , a2)
toProduct l r = to (view l &&& view r)
{-# INLINE toProduct #-}

-- | Combine two 'Review's into a 'Review' from a sum.
--
-- @
-- 'fromSum' :: 'Review' t b1 -> 'Review' t b2 -> 'Review' t (b1 + b2)
-- @
--
fromSum :: AReview t b1 -> AReview t b2 -> Review t (b1 + b2)
fromSum l r = from (review l ||| review r)
{-# INLINE fromSum #-}

---------------------------------------------------------------------
-- Indexed optics 
---------------------------------------------------------------------

-- | TODO: Document
--
-- @since 0.0.3
ixto :: (s -> (k , a)) -> Ixview k s a
ixto f = coercer . lmap (f . snd)
{-# INLINE ixto #-}

-- | TODO: Document
--
-- @since 0.0.3
ixlike :: k -> a -> Ixview k s a
ixlike k a = ixto (const (k, a))
{-# INLINE ixlike #-}

-- | TODO: Document
--
-- >>> cofoldsWithKey (rxfrom Map.mapWithKey # rxfrom Map.mapWithKey) (\k r a -> Map.singleton k (a + r)) 1.0 $ Map.fromList [("k",Map.fromList [("l",2.0)])]
-- fromList [("k",fromList [("l",fromList [("kl",3.0)])])]
--
-- @since 0.0.3
rxfrom :: ((k -> b) -> t) -> Rxview k t b
rxfrom f = coercel . rmap (\ib _ -> f ib)
{-# INLINE rxfrom #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

infix 8 ^.

-- | An infix alias for 'view'.
--
-- Fiity and semantics are such that subsequent field accesses can be
-- performed with ('Prelude..').
--
-- >>> ("hello","world") ^. second'
-- "world"
--
-- >>> 5 ^. to succ
-- 6
--
-- >>> import Data.Complex
-- >>> ((0, 1 :+ 2), 3) ^. first' . second' . to magnitude
-- 2.23606797749979
--
(^.) :: s -> AView a s a -> a
(^.) = flip view
{-# INLINE ( ^. ) #-}

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
views o f = asks $ folds o f
{-# INLINE views #-}

infix 8 ^%

-- | View the focus of an indexed optic along with its index.
--
-- /Note/: if the optic focuses on more than one element, then
-- the returned index will be a monoidal sum of all indices visited.
--
-- >>> [("foo",41), ("bar",42), ("baz",43)] ^% ix "yo" traversed . ixfirst
-- (Just "yoyoyo","foobarbaz")
--
-- @since 0.0.3
(^%) :: Monoid k => s -> AIxview k s a -> (Maybe k, a)
(^%) = flip viewWithKey
{-# INLINE (^%) #-}

-- | A prefix alias for '^%'.
--
-- >>> viewWithKey ixfirst ("foo", 42) :: (Maybe (Sum Int), String)
-- (Just (Sum {getSum = 0}),"foo")
--
-- @since 0.0.3
viewWithKey :: MonadReader s m => Monoid k => AIxview k s a -> m (Maybe k , a)
viewWithKey o = viewsWithKey o $ \k a -> (Just k, a)
{-# INLINE viewWithKey #-}

-- | Bring a function of the index and value of an indexed optic into the current environment.
--
-- Use 'viewWithKey' if there is a need to disambiguate between 'mempty' as a miss vs. as a return value.
--
-- @since 0.0.3
viewsWithKey :: MonadReader s m => Monoid k => Ixoptic' (Star (Const r)) k s a -> (k -> a -> r) -> m r
viewsWithKey o f = asks $ foldsWithKey o f
{-# INLINE viewsWithKey #-}

infix 8 .^

-- | An infix alias of 'review'.
--
-- >>> from succ .^ 5
-- 6
--
(.^) :: AReview t b -> b -> t
(.^) = review
{-# INLINE (.^) #-}

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

-- | Bring a function of the index of a co-indexed optic into the current environment.
--
-- @since 0.0.3
reviewWithKey :: ARxview k t b -> b -> (k -> t)
reviewWithKey o = reviewsWithKey o id
{-# INLINE reviewWithKey #-}

-- | Bring a continuation of the index of a co-indexed optic into the current environment.
--
-- @
-- reviewsWithKey :: ARxview k t b -> ((k -> t) -> r) -> b -> r
-- @
--
-- @since 0.0.3
reviewsWithKey :: ARxview k t b -> ((k -> t) -> r) -> b -> r
reviewsWithKey o f = unwrap o f . const where unwrap o1 f1 = f1 . unTagged #. o1 .# Tagged
{-# INLINE reviewsWithKey #-}

---------------------------------------------------------------------
-- MonadState
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

{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE FlexibleContexts      #-}
module Data.Profunctor.Optic.View (
    -- * Constructors
    View, Ixview
  , to
  , ixto
  , like
  , ixlike
  , cloneView
  , cloneIxview
    -- * Dual Constructors
    -- ** Coview, Cxview
  , Coview, Cxview
  , from
  , cxfrom
  , unlike
  , cloneCoview
    -- ** Review, Rxview
    -- * Optics
  , tupling
    -- * Dual Optics
  , summing
    -- * Operators
  , view
  , ixview
  , views
  , ixviews
  , viewing
    -- * Dual Operators
  , coview
  , cxview
  , coviews
  , cxviews
    -- * MonadState
  , use
  , ixuse
  , uses
  , ixuses
  , couse
  , cxuse
  , couses
  , cxuses
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

-- | TODO: Document
--
-- @since 0.0.3
ixto :: (s -> (k , a)) -> Ixview k s a
ixto f = coercedR . lmap (f . snd)
{-# INLINE ixto #-}

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
-- @since 0.0.3
ixlike :: k -> a -> Ixview k s a
ixlike k a = ixto (const (k, a))
{-# INLINE ixlike #-}

-- | TODO: Document
--
-- @
-- 'cloneView' :: 'Monoid' a => 'AView' a s a -> 'Fold' s a
-- @
--
cloneView :: AView a s a -> View s a
cloneView o = to (view o)
{-# INLINE cloneView #-}

-- | Clone an indexed 'View'.
--
-- @since 0.0.3
cloneIxview :: Monoid k => AIxview k s a -> View s (Maybe k, a)
cloneIxview o = to (ixview o)
{-# INLINE cloneIxview #-}

---------------------------------------------------------------------
-- ** Dual Constructors
-- Note: 'Review' here is the co-dual of 'View' (@Closed + CoercingL@),
-- which should properly be called @Coview@. The true Re-dual @Review@
-- (@Costrong + CoercingL@) will be added in a future release (S17.28).
---------------------------------------------------------------------

-- | Obtain a 'Coview' from an arbitrary function.
--
-- @
-- 'from' f ≡ 'iso' f 'id' -- restricted to 'Coview'
-- @
--
-- >>> coview (from Prelude.length) [1,2,3]
-- 3
--
-- @
-- 'from' :: (b -> t) -> 'Coview' t b
-- @
--
from :: (b -> t) -> Coview t b
from f = coercedL . rmap f
{-# INLINE from #-}

-- | TODO: Document
--
-- >>> cxfoldMapOf (cxfrom Map.mapWithKey # cxfrom Map.mapWithKey) (\k r a -> Map.singleton k (a + r)) 1.0 $ Map.fromList [("k",Map.fromList [("l",2.0)])]
-- fromList [("k",fromList [("l",fromList [("kl",3.0)])])]
--
-- @since 0.0.3
cxfrom :: ((k -> b) -> t) -> Cxview k t b
cxfrom f = coercedL . rmap (\ib _ -> f ib)
{-# INLINE cxfrom #-}

-- | Obtain a constant-valued (index-preserving) 'Coview' from an arbitrary value.
--
-- @
-- 'unlike' a '.' 'unlike' b ≡ 'unlike' a
-- 'unlike' a '.^' b ≡ a
-- 'unlike' a '.^' b ≡ 'from' ('const' a) '#' b
-- @
--
unlike :: t -> Coview t b
unlike t = from (const t)
{-# INLINE unlike #-}

-- | TODO: Document
--
cloneCoview :: ACoview t b -> Coview t b
cloneCoview o = from (coview o)
{-# INLINE cloneCoview #-}

-- TODO: cloneCxview — needs investigation into Cxoptic' Tagged path

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
-- ** Dual Optics
---------------------------------------------------------------------

-- | Combine two 'Coview's into a 'Coview' from a sum.
--
-- @
-- 'summing' :: 'Coview' t b1 -> 'Coview' t b2 -> 'Coview' t (b1 + b2)
-- @
--
summing :: ACoview t b1 -> ACoview t b2 -> Coview t (b1 + b2)
summing l r = from (either (coview l) (coview r))
{-# INLINE summing #-}

---------------------------------------------------------------------
-- * Operators
---------------------------------------------------------------------

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
view = flip views id
{-# INLINE view #-}

-- | View the focus of an indexed optic along with its index.
--
-- >>> ixview ixfirst ("foo", 42) :: (Maybe (Sum Int), String)
-- (Just (Sum {getSum = 0}),"foo")
--
-- @since 0.0.3
ixview :: MonadReader s m => Monoid k => AIxview k s a -> m (Maybe k , a)
ixview o = ixviews o $ \k a -> (Just k, a)
{-# INLINE ixview #-}

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

-- | Bring a function of the index and value of an indexed optic into the current environment.
--
-- Use 'ixview' if there is a need to disambiguate between 'mempty' as a miss vs. as a return value.
--
-- @since 0.0.3
ixviews :: MonadReader s m => Monoid k => Ixoptic' (Star (Const r)) k s a -> (k -> a -> r) -> m r
ixviews o f = asks $ ixfoldMapOf o f
{-# INLINE ixviews #-}

-- | Obtain a 'View' from an 'AFold0'.
--
-- @'viewing' ≡ 'to' '.' 'preview'@
--
viewing :: AFold0 a s a -> View s (Maybe a)
viewing o = coercedR . lmap (preview o)
{-# INLINE viewing #-}

---------------------------------------------------------------------
-- ** Dual Operators
---------------------------------------------------------------------

-- | Coview the focus of an optic.
--
-- @
-- 'coview' . 'from' ≡ 'id'
-- @
--
-- >>> coview left' 4
-- Left 4
--
coview :: ACoview t b -> b -> t
coview o = coviews o id
{-# INLINE coview #-}

-- | Bring a function of the index of a co-indexed optic into the current environment.
--
-- @since 0.0.3
cxview :: ACxview k t b -> b -> (k -> t)
cxview o = cxviews o id
{-# INLINE cxview #-}

-- | Turn an optic around and look through the other end, applying a function.
--
-- @
-- 'coviews' ('from' f) g ≡ g '.' f
-- @
--
-- >>> coviews left isRight "mustard"
-- False
-- >>> coviews (from succ) (*2) 3
-- 8
--
coviews :: ACoview t b -> (t -> r) -> b -> r
coviews o f = f . unTagged #. o .# Tagged
{-# INLINE coviews #-}

-- | Bring a continuation of the index of a co-indexed optic into the current environment.
--
-- @
-- cxviews :: ACxview k t b -> ((k -> t) -> r) -> b -> r
-- @
--
-- @since 0.0.3
cxviews :: ACxview k t b -> ((k -> t) -> r) -> b -> r
cxviews o f = unwrap o f . const where unwrap o1 f1 = f1 . unTagged #. o1 .# Tagged
{-# INLINE cxviews #-}

---------------------------------------------------------------------
-- * MonadState
---------------------------------------------------------------------

-- | TODO: Document
--
use :: MonadState s m => AView a s a -> m a
use o = gets (view o)
{-# INLINE use #-}

-- | Indexed 'use': view the focus of an indexed optic in the current state.
--
-- @since 0.0.3
ixuse :: MonadState s m => Monoid k => AIxview k s a -> m (Maybe k, a)
ixuse o = gets (ixview o)
{-# INLINE ixuse #-}

-- | Use the target of an optic in the current state.
--
-- >>> evalState (uses first length) ("hello","world!")
-- 5
--
uses :: MonadState s m => AFold r s a -> (a -> r) -> m r
uses l f = gets (views l f)
{-# INLINE uses #-}

-- | Indexed 'uses': apply an indexed function to the focus in the current state.
--
-- @since 0.0.3
ixuses :: MonadState s m => Monoid k => Ixoptic' (Star (Const r)) k s a -> (k -> a -> r) -> m r
ixuses o f = gets (ixviews o f)
{-# INLINE ixuses #-}

-- | Turn an optic around and 'use' a value (or the current environment) through it the other way.
--
-- @
-- 'couse' '.' 'from' ≡ 'gets'
-- @
--
-- >>> evalState (couse left) 5
-- Left 5
-- >>> evalState (couse (from succ)) 5
-- 6
--
couse :: MonadState b m => ACoview t b -> m t
couse o = gets (unTagged #. o .# Tagged)
{-# INLINE couse #-}

-- | Turn an optic around and 'use' the current state through it the other way, applying a function.
--
-- @
-- 'couses' ('from' f) g ≡ 'gets' (g '.' f)
-- @
--
-- >>> evalState (couses left isLeft) (5 :: Int)
-- True
--
couses :: MonadState b m => ACoview t b -> (t -> r) -> m r
couses o tr = gets (tr . unTagged #. o .# Tagged)
{-# INLINE couses #-}

-- | Coindexed 'couse': build a coindexed value from the current state.
--
-- @since 0.0.3
cxuse :: MonadState b m => ACxview k t b -> m (k -> t)
cxuse o = gets (cxview o)
{-# INLINE cxuse #-}

-- | Coindexed 'couses': apply a coindexed function from the current state.
--
-- @since 0.0.3
cxuses :: MonadState b m => ACxview k t b -> ((k -> t) -> r) -> m r
cxuses o f = gets (cxviews o f)
{-# INLINE cxuses #-}

{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE FlexibleContexts      #-}

-- | Left and right carriers are characterized by their representation
-- functors ('Rep' and 'Corep'). 'Iso' sits at the top where both
-- are trivial ('Identity'). 'Adjoint' sits at the bottom where they
-- form a full adjunction (@'Corep' p ⊣ 'Rep' p@). A left-indexed
-- ('Ix') optic threads an index through the left adjoint functor
-- @(,) k@, while a right-indexed ('Cx') optic threads a coindex
-- through the right adjoint functor @(->) k@.
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
    -- ** Review
  , Review
  , reinto
  , cloneReview
    -- * Optics
  , tupling
  , ixtupling
    -- * Dual Optics
  , summing
    -- * Operators
  , view
  , ixview
  , views
  , ixviews
  , viewing
    -- * Dual Operators
  , review
  , cxview
  , reviews
  , cxviews
    -- * MonadState
  , use
  , ixuse
  , uses
  , ixuses
  , reuse
  , cxuse
  , reuses
  , cxuses
) where

import Control.Monad.Reader as Reader
import Control.Monad.State as State
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Types
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
cloneIxview :: Monoid k => AIxview k s a -> View s (k, a)
cloneIxview o = to (ixview o)
{-# INLINE cloneIxview #-}

---------------------------------------------------------------------
-- ** Dual Constructors
--
-- 'View' has two duals:
--
-- * 'Coview' (@Closed + CoercingL@) — the Star\/Costar dual,
--   composing with the Closed chain (Colens, Cotraversal, Cofold).
-- * 'Review' (@Costrong + CoercingL@) — the Strong\/Costrong
--   (Re-)dual, composing with the Costrong chain (Relens, Grate).
--
-- At the operator level only 'review' is provided. Both 'Coview'
-- and 'Review' monomorphize to the same carrier ('Tagged'), so
-- 'review' accepts either after monomorphization. Passing a
-- polymorphic @'Coview' t b@ to 'review' directly will not
-- typecheck — 'Closed' does not imply 'Costrong'.
--
-- For the coindexed case, only 'cxview' is provided (not @rxview@).
-- 'Cxview' threads the coindex via @k -> b@ on the right of the
-- profunctor ('Cxoptic''), which survives through 'Tagged' and
-- produces an observable @b -> (k -> t)@. The hypothetical @Rxview@
-- threads via @(k, b)@ on the left ('Ixoptic''), which 'Tagged'
-- discards — collapsing to plain 'review'.
--
-- For the relationship between these two duality axes, see
-- "Data.Profunctor.Optic.Dual".
---------------------------------------------------------------------

-- | Obtain a 'Coview' from an arbitrary function.
--
-- @
-- 'from' f ≡ 'iso' f 'id' -- restricted to 'Coview'
-- @
--
-- >>> review (from Prelude.length) [1,2,3]
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
cloneCoview o = from (review o)
{-# INLINE cloneCoview #-}

-- TODO: cloneCxview — needs investigation into Cxoptic' Tagged path

-- | Obtain a 'Review' from a function.
--
-- @
-- 'reinto' f ≡ 're' ('to' f)
-- @
--
-- 'reinto' is the 'Re'-dual of 'to': where 'to' builds a 'View'
-- from a getter @s -> a@, 'reinto' builds a 'Review' from a
-- constructor @b -> t@. Both 'reinto' and 'from' accept the same
-- argument, but return different types: 'from' returns 'Coview'
-- ('Closed' + 'CoercingL') while 'reinto' returns 'Review'
-- ('Costrong' + 'CoercingL'). At the carrier level ('Tagged')
-- they are interchangeable.
--
reinto :: (b -> t) -> Review t b
reinto f = coercedL . rmap f
{-# INLINE reinto #-}

-- | Clone a 'Review'.
--
cloneReview :: AReview t b -> Review t b
cloneReview o = reinto (review o)
{-# INLINE cloneReview #-}

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

-- | Combine two indexed 'View's into an indexed 'View' to a product.
--
-- @
-- 'ixtupling' :: 'Monoid' k => 'AIxview' k s a1 -> 'AIxview' k s a2 -> 'Ixview' k s (a1 , a2)
-- @
--
-- @since 0.0.3
ixtupling :: Monoid k => AIxview k s a1 -> AIxview k s a2 -> Ixview k s (a1 , a2)
ixtupling l r = ixto $ \s ->
  let (k1, a1) = ixview l s
      (k2, a2) = ixview r s
  in  (k1 <> k2, (a1, a2))
{-# INLINE ixtupling #-}

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
summing l r = from (either (review l) (review r))
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
-- >>> ixview ixfirst ("foo", 42) :: (Sum Int, String)
-- (Sum {getSum = 0},"foo")
--
-- @since 0.0.3
ixview :: MonadReader s m => Monoid k => AIxview k s a -> m (k, a)
ixview o = ixviews o (,)
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
-- See also 'ixview' which returns @(k, a)@ directly.
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
--
-- 'review' is the Re-dual of 'view' (Strong/Costrong duality).
-- Its type is @'AReview' t b -> b -> t@, where @'AReview' = 'Optic''
-- 'Tagged' t b@. Since 'Tagged' is both 'Closed' and 'Costrong',
-- 'review' also accepts 'Coview' optics (the Star/Costar dual of
-- 'View'). A polymorphic 'Coview' will require a type annotation or
-- monomorphization to pass to 'review', since 'Closed' does not
-- imply 'Costrong'.
--
-- 'cxview' is the coindexed variant. There is no @rxview@ because
-- the @Rx@ coindex threads via @(k, -)@ on the left of the
-- profunctor, which 'Tagged' discards — see "Dual Constructors".
---------------------------------------------------------------------

-- | The Re-dual of 'view': build a structure from a value.
--
-- @
-- 'review' . 'from' ≡ 'id'
-- @
--
-- >>> review left' 4
-- Left 4
--
-- 'review' is typed at 'AReview' (@Costrong + CoercingL@ monomorphized
-- to 'Tagged'). Since 'Tagged' also satisfies 'Closed', 'review'
-- accepts 'Coview' optics as well — but only after monomorphization.
-- Passing a polymorphic @'Coview' t b@ directly will not typecheck,
-- because 'Closed' does not imply 'Costrong'.
--
review :: AReview t b -> b -> t
review o = reviews o id
{-# INLINE review #-}

-- | Coindexed review: build a coindexed value from a value.
--
-- The coindex @k@ threads via @k -> b@ on the right of the profunctor
-- ('Cxoptic''), producing an observable @b -> (k -> t)@. This is the
-- only coindexed Re-dual view operator — the hypothetical @rxview@
-- would thread the coindex via @(k, b)@ on the left ('Ixoptic''),
-- but 'Tagged' discards the left component, collapsing to 'review'.
--
-- @since 0.0.3
cxview :: ACxview k t b -> b -> (k -> t)
cxview o = cxviews o id
{-# INLINE cxview #-}

-- | Turn an optic around and look through the other end, applying a function.
--
-- @
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

-- | Coindexed 'reviews': apply a function to the coindexed result.
--
-- There is no @rxviews@ for the same reason there is no @rxview@:
-- the @Rx@ coindex threads via @(k, -)@ on the left of the profunctor
-- ('Ixoptic''), which 'Tagged' discards, collapsing to 'reviews'.
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
ixuse :: MonadState s m => Monoid k => AIxview k s a -> m (k, a)
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
-- 'reuses' ('from' f) g ≡ 'gets' (g '.' f)
-- @
--
-- >>> evalState (reuses left isLeft) (5 :: Int)
-- True
--
reuses :: MonadState b m => AReview t b -> (t -> r) -> m r
reuses o tr = gets (tr . unTagged #. o .# Tagged)
{-# INLINE reuses #-}

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

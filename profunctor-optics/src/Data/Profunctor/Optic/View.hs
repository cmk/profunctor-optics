{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TupleSections         #-}
module Data.Profunctor.Optic.View (
    -- * Types
    View
  , Ixview
  , PrimView
  , Review
  , Cxview
  , PrimReview
    -- * Constructors
  , to
  , ito
  , from
  , kfrom
  , cloneView
  , cloneReview
    -- * Optics
  , like
  , ilike
  , relike
  , klike
  , toProduct
  , fromSum
    -- * Primitive operators
  , withPrimView
  , withPrimReview
    -- * Operators
  , (^.)
  , (^%)
  , view
  , iview
  , views
  , iviews
  , use
  , iuse
  , uses
  , iuses
  , (#^)
  , review
  , kview
  , reviews
  , kviews
  , reuse
  , reuses
  , kuse
  , kuses
    -- * MonadIO
  , throws
  , throws_
  , throwsTo
) where

import Control.Exception (Exception)
import Control.Monad.IO.Class
import Control.Monad.Reader as Reader
import Control.Monad.Writer as Writer hiding (Sum(..))
import Control.Monad.State as State
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Operator
import Data.Profunctor.Optic.Import
import GHC.Conc (ThreadId)
import qualified Control.Exception as Ex
import qualified Data.Bifunctor as B

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> :set -XRank2Types
-- >>> import Data.Either
-- >>> import Control.Monad.State
-- >>> import Control.Monad.Writer
-- >>> import Data.Int.Instance ()
-- >>> import Data.List.Index as LI
-- >>> :load Data.Profunctor.Optic Data.Either.Optic Data.Tuple.Optic
-- >>> let catchOn :: Int -> Cxprism' Int (Maybe String) String ; catchOn n = kjust $ \k -> if k==n then Just "caught" else Nothing
-- >>> let itraversed :: Ixtraversal Int [a] [b] a b ; itraversed = itraversalVl itraverse
-- >>> let iat :: Int -> Ixaffine' Int [a] a; iat i = iaffine' (\s -> flip LI.ifind s $ \n _ -> n==i) (\s a -> LI.modifyAt i (const a) s) 

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
to :: (s -> a) -> PrimView s t a b
to f = coercer . lmap f
{-# INLINE to #-}

-- | TODO: Document
--
ito :: (s -> (i , a)) -> Ixview i s a
ito f = to $ f . snd
{-# INLINE ito #-}

-- | Obtain a 'Review' from an arbitrary function.
--
-- @
-- 'from' ≡ 're' . 'to'
-- @
--
-- >>> (from Prelude.length) #^ [1,2,3]
-- 3
--
-- @
-- 'from' :: (b -> t) -> 'Review' t b
-- @
--
from :: (b -> t) -> PrimReview s t a b 
from f = coercel . rmap f
{-# INLINE from #-}

-- | TODO: Document
--
kfrom :: ((k -> b) -> t) -> Cxview k t b
kfrom f = from $ \kb _ -> f kb
{-# INLINE kfrom #-}

-- | TODO: Document
--
-- @
-- 'cloneView' ::             'AView' s a -> 'View' s a
-- 'cloneView' :: 'Monoid' a => 'AView' s a -> 'Fold' s a
-- @
--
cloneView :: AView s a -> PrimView s s a a
cloneView = to . view
{-# INLINE cloneView #-}

-- | TODO: Document
--
cloneReview :: AReview t b -> PrimReview t t b b
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
like :: a -> PrimView s t a b
like = to . const
{-# INLINE like #-}

-- | TODO: Document
--
ilike :: i -> a -> Ixview i s a
ilike i a = ito (const (i, a))
{-# INLINE ilike #-}

-- | Obtain a constant-valued (index-preserving) 'Review' from an arbitrary value.
--
-- @
-- 'relike' a '.' 'relike' b ≡ 'relike' a
-- 'relike' a '#' b ≡ a
-- 'relike' a '#' b ≡ 'from' ('const' a) '#' b
-- @
--
relike :: t -> PrimReview s t a b
relike = from . const
{-# INLINE relike #-}

-- | Obtain a constant-valued 'Cxview' from an arbitrary value. 
--
klike :: t -> Cxview k t b
klike = kfrom . const
{-# INLINE klike #-}

-- | Combine two 'View's into a 'View' to a product.
--
-- @
-- 'toProduct' :: 'View' s a1 -> 'View' s a2 -> 'View' s (a1 , a2)
-- @
--
toProduct :: AView s a1 -> AView s a2 -> PrimView s t (a1 , a2) b
toProduct l r = to (view l &&& view r)
{-# INLINE toProduct #-}

-- | Combine two 'Review's into a 'Review' from a sum.
--
-- @
-- 'fromSum' :: 'Review' t b1 -> 'Review' t b2 -> 'Review' t (b1 + b2)
-- @
--
fromSum :: AReview t b1 -> AReview t b2 -> PrimReview s t a (b1 + b2)
fromSum l r = from (review l ||| review r)
{-# INLINE fromSum #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | A prefix alias for '^.'.
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
view :: MonadReader s m => AView s a -> m a
view o = views o id
{-# INLINE view #-}

-- | A prefix alias for '^%'.
--
-- >>> iview ifirst ("foo", 42)
-- (Just (),"foo")
--
-- >>> iview (iat 3 . ifirst) [(0,'f'),(1,'o'),(2,'o'),(3,'b'),(4,'a'),(5,'r') :: (Int, Char)]
-- (Just 3,3)
--
-- In order to 'iview' a 'Choice' optic (e.g. 'Ixaffine', 'Ixtraversal', 'Ixfold', etc),
-- /a/ must have a 'Monoid' instance:
--
-- >>> iview (iat 0) ([] :: [Int])
-- (Nothing,0)
-- >>> iview (iat 0) ([1] :: [Int])
-- (Just 0,1)
--
-- /Note/ when applied to a 'Ixtraversal' or 'Ixfold', then 'iview' will return a monoidal 
-- summary of the indices tupled with a monoidal summary of the values:
--
-- >>> (iview @_ @_ @Int @Int) itraversed [1,2,3,4]
-- (Just 6,10)
--
iview :: MonadReader s m => Monoid i => AIxview i s a -> m (Maybe i , a)
iview o = asks $ withPrimView o (B.first Just) . (mempty,)
{-# INLINE iview #-}

-- | Map each part of a structure viewed to a semantic editor combinator.
--
-- @
-- 'views o f ≡ withFold o f'
-- 'Data.Foldable.foldMap' = 'views' 'folding''
-- @
--
-- >>> views both id (["foo"], ["bar", "baz"])
-- ["foo","bar","baz"]
--
-- @
-- 'views' ::                'AView' s a       -> (a -> r) -> s -> r
-- 'views' ::                'Iso'' s a        -> (a -> r) -> s -> r
-- 'views' ::                'Lens'' s a       -> (a -> r) -> s -> r
-- 'views' ::                'Coprism'' s a    -> (a -> r) -> s -> r
-- 'views' :: 'Monoid' r    => 'Traversal'' s a  -> (a -> r) -> s -> r
-- 'views' :: 'Semigroup' r => 'Traversal1'' s a -> (a -> r) -> s -> r
-- 'views' :: 'Monoid' r    => 'Fold' s a        -> (a -> r) -> s -> r
-- 'views' :: 'Semigroup' r => 'Fold1' s a       -> (a -> r) -> s -> r
-- @
--
views :: MonadReader s m => Optic' (Star (Const r)) s a -> (a -> r) -> m r
views o f = asks $ withPrimView o f
{-# INLINE views #-}

-- | Bring a function of the index and value of an indexed optic into the current environment.
--
-- 'iviews' ≡ 'iwithFold'
--
-- >>> iviews (iat 2) (-) ([0,1,2] :: [Int])
-- 0
--
-- In order to 'iviews' a 'Choice' optic (e.g. 'Ixaffine', 'Ixtraversal', 'Ixfold', etc),
-- /a/ must have a 'Monoid' instance (here from the 'rings' package):
--
-- >>> iviews (iat 3) (flip const) ([1] :: [Int])
-- 0
--
-- Use 'iview' if there is a need to disambiguate between 'mempty' as a miss vs. as a return value.
--
iviews :: MonadReader s m => Monoid i => IndexedOptic' (Star (Const r)) i s a -> (i -> a -> r) -> m r
iviews o f = asks $ withPrimView o (uncurry f) . (mempty,) 

-- | TODO: Document
--
use :: MonadState s m => AView s a -> m a
use o = gets (view o)
{-# INLINE use #-}

-- | Bring the index and value of an indexed optic into the current environment as a pair.
--
iuse :: MonadState s m => Monoid i => AIxview i s a -> m (Maybe i , a)
iuse o = gets (iview o)

-- | Use the target of a 'Lens', 'Data.Profunctor.Optic.Iso.Iso' or
-- 'View' in the current state, or use a summary of a
-- 'Data.Profunctor.Optic.Fold.Fold' or 'Data.Profunctor.Optic.Traversal.Traversal' that
-- points to a monoidal value.
--
-- >>> evalState (uses first' length) ("hello","world!")
-- 5
--
-- @
-- 'uses' :: 'MonadState' s m             => 'Data.Profunctor.Optic.Iso.Iso'' s a       -> (a -> r) -> m r
-- 'uses' :: 'MonadState' s m             => 'Data.Profunctor.Optic.View.View' s a     -> (a -> r) -> m r
-- 'uses' :: 'MonadState' s m             => 'Data.Profunctor.Optic.Lens.Lens'' s a      -> (a -> r) -> m r
-- 'uses' :: 'MonadState' s m             => 'Data.Profunctor.Optic.Prism.Coprism'' s a      -> (a -> r) -> m r
-- 'uses' :: 'MonadState' s m => 'Data.Monoid.Monoid' r => 'Data.Profunctor.Optic.Traversal.Traversal'' s a -> (a -> r) -> m r
-- 'uses' :: 'MonadState' s m => 'Data.Monoid.Monoid' r => 'Data.Profunctor.Optic.Fold.Fold' s a       -> (a -> r) -> m r
-- @
--
-- @
-- 'uses' :: 'MonadState' s m => 'Getting' r s t a b -> (a -> r) -> m r
-- @
--
uses :: MonadState s m => Optic' (Star (Const r)) s a -> (a -> r) -> m r
uses l f = gets (views l f)
{-# INLINE uses #-}

-- | Bring a function of the index and value of an indexed optic into the current environment.
--
iuses :: MonadState s m => Monoid i => IndexedOptic' (Star (Const r)) i s a -> (i -> a -> r) -> m r
iuses o f = gets $ withPrimView o (uncurry f) . (mempty,)

-- | A prefix alias of '#^'.
--
-- @
-- 'review' ≡ 'view' '.' 're'
-- 'review' . 'from' ≡ 'id'
-- @
--
-- >>> review (from succ) 5
-- 6
--
-- @
-- 'review' :: 'Iso'' s a   -> a -> s
-- 'review' :: 'Prism'' s a -> a -> s
-- 'review' :: 'Colens'' s a -> a -> s
-- @
--
review :: MonadReader b m => AReview t b -> m t
review o = reviews o id
{-# INLINE review #-}

-- | Bring a function of the index of a co-indexed optic into the current environment.
--
kview :: MonadReader b m => ACxview k t b -> m (k -> t)
kview o = kviews o id
{-# INLINE kview #-}

-- | Turn an optic around and look through the other end, applying a function.
--
-- @
-- 'reviews' ≡ 'views' '.' 're'
-- 'reviews' ('from' f) g ≡ g '.' f
-- @
--
-- >>> reviews left' isRight "mustard"
-- False
--
-- >>> reviews (from succ) (*2) 3
-- 8
--
-- @
-- 'reviews' :: 'Iso'' t b -> (t -> r) -> b -> r
-- 'reviews' :: 'Prism'' t b -> (t -> r) -> b -> r
-- 'reviews' :: 'Colens'' t b -> (t -> r) -> b -> r
-- @
--
reviews :: MonadReader b m => AReview t b -> (t -> r) -> m r
reviews o f = asks $ withPrimReview o f
{-# INLINE reviews #-}

-- | Bring a continuation of the index of a co-indexed optic into the current environment.
--
-- @
-- kviews :: ACxview k t b -> ((k -> t) -> r) -> b -> r
-- @
--
kviews :: MonadReader b m => ACxview k t b -> ((k -> t) -> r) -> m r
kviews o f = asks $ withPrimReview o f . const

-- | Turn an optic around and 'use' a value (or the current environment) through it the other way.
--
-- @
-- 'reuse' ≡ 'use' '.' 're'
-- 'reuse' '.' 'from' ≡ 'gets'
-- @
--
-- >>> evalState (reuse left') 5
-- Left 5
--
-- >>> evalState (reuse (from succ)) 5
-- 6
--
-- @
-- 'reuse' :: 'MonadState' a m => 'Iso'' s a   -> m s
-- 'reuse' :: 'MonadState' a m => 'Prism'' s a -> m s
-- 'reuse' :: 'MonadState' a m => 'Colens'' s a -> m s
-- @
--
reuse :: MonadState b m => AReview t b -> m t
reuse o = gets (unTagged #. o .# Tagged)
{-# INLINE reuse #-}

-- | TODO: Document
--
kuse :: MonadState b m => ACxview k t b -> m (k -> t)
kuse o = gets (kview o)
{-# INLINE kuse #-}

-- | Turn an optic around and 'use' the current state through it the other way, applying a function.
--
-- @
-- 'reuses' ≡ 'uses' '.' 're'
-- 'reuses' ('from' f) g ≡ 'gets' (g '.' f)
-- @
--
-- >>> evalState (reuses left' isLeft) (5 :: Int)
-- True
--
-- @
-- 'reuses' :: 'MonadState' a m => 'Iso'' s a   -> (s -> r) -> m r
-- 'reuses' :: 'MonadState' a m => 'Prism'' s a -> (s -> r) -> m r
-- 'reuses' :: 'MonadState' a m => 'Prism'' s a -> (s -> r) -> m r
-- @
--
reuses :: MonadState b m => AReview t b -> (t -> r) -> m r
reuses o tr = gets (tr . unTagged #. o .# Tagged)
{-# INLINE reuses #-}

-- | TODO: Document
--
kuses :: MonadState b m => ACxview k t b -> ((k -> t) -> r) -> m r
kuses o f = gets (kviews o f)
{-# INLINE kuses #-}

---------------------------------------------------------------------
-- 'MonadIO'
---------------------------------------------------------------------

-- | Throw an exception described by an optic.
--
-- @
-- 'throws' o e \`seq\` x  ≡ 'throws' o e
-- @
--
throws :: MonadIO m => Exception e => AReview e b -> b -> m r
throws o = reviews o $ liftIO . Ex.throwIO
{-# INLINE throws #-}

-- | Variant of 'throws' for error constructors with no arguments.
--
throws_ :: MonadIO m => Exception e => AReview e () -> m r
throws_ o = throws o ()

-- | Raise an 'Exception' specified by an optic in the target thread.
--
-- @
-- 'throwsTo' thread o ≡ 'throwTo' thread . 'review' o
-- @
--
throwsTo :: MonadIO m => Exception e => ThreadId -> AReview e b -> b -> m ()
throwsTo tid o = reviews o (liftIO . Ex.throwTo tid)

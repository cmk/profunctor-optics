{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
module Data.Profunctor.Optic.View (
    -- * Types
    View
  , AView
  , PrimView
  , Review
  , AReview
  , PrimReview
    -- * Constructors
  , to
  , from
  , toProduct
  , fromSum
  , cloneView 
  , cloneReview
    -- * Representatives
  , Tagged(..)
    -- * Primitive operators
  , views
  , reviews
    -- * Common optics
  , like
  , relike
    -- * Derived operators
  , view 
  , review
  , (^.)
  , (#)
    -- * MonadIO
  , throws
  , throws_
  , throwsTo
    -- * MonadState & MonadWriter
  , use
  , reuse
  , uses 
  , reuses
  , listening
  , listenings
) where

import Control.Exception (Exception)
import Control.Monad.IO.Class
import Control.Monad.Reader as Reader
import Control.Monad.Writer as Writer hiding (Sum(..))
import Control.Monad.State as State hiding (StateT(..))
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Import
import GHC.Conc (ThreadId)
import qualified Control.Exception as Ex

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> import Data.Either
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
-- >>> (0, -5) ^. second . to abs
-- 5
--
-- @
-- 'to' :: (s -> a) -> 'View' s a
-- @
--
to :: (s -> a) -> PrimView s t a b
to f = coercer . lmap f
{-# INLINE to #-}

-- | Obtain a 'Review' from an arbitrary function.
--
-- @
-- 'from' ≡ 're' . 'to'
-- @
--
-- >>> (from Prelude.length) # [1,2,3]
-- 3
--
-- @
-- 'from' :: (b -> t) -> 'Review' t b
-- @
--
from :: (b -> t) -> PrimReview s t a b 
from f = coercel . rmap f
{-# INLINE from #-}

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
-- Primitive operators
---------------------------------------------------------------------

-- | Map each part of a structure viewed to a semantic editor combinator.
--
-- @
-- 'views o f ≡ foldMapOf o f'
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
-- 'views' ::                'Reprism'' s a    -> (a -> r) -> s -> r
-- 'views' :: 'Monoid' r    => 'Traversal'' s a  -> (a -> r) -> s -> r
-- 'views' :: 'Semigroup' r => 'Traversal1'' s a -> (a -> r) -> s -> r
-- 'views' :: 'Monoid' r    => 'Fold' s a        -> (a -> r) -> s -> r
-- 'views' :: 'Semigroup' r => 'Fold1' s a       -> (a -> r) -> s -> r
-- @
--
views :: MonadReader s m => Optic' (FoldRep r) s a -> (a -> r) -> m r
views o f = asks ((getConst #.) #. runStar #. o .# Star .# (Const #.) $ f)
{-# INLINE views #-}

-- | Turn an optic around and look through the other end, applying a function.
--
-- @
-- 'reviews' ≡ 'views' '.' 're'
-- 'reviews' ('from' f) g ≡ g '.' f
-- @
--
-- >>> reviews left isRight "mustard"
-- False
--
-- >>> reviews (from succ) (*2) 3
-- 8
--
-- @
-- 'reviews' :: 'Iso'' s a   -> (s -> r) -> a -> r
-- 'reviews' :: 'Prism'' s a -> (s -> r) -> a -> r
-- 'reviews' :: 'Relens'' s a -> (s -> r) -> a -> r
-- @
--
reviews :: MonadReader b m => AReview t b -> (t -> r) -> m r
reviews p f = asks (f . unTagged #. p .# Tagged)
{-# INLINE reviews #-}

---------------------------------------------------------------------
-- Common 'View's and 'Review's
---------------------------------------------------------------------

-- | Obtain a constant-valued (index-preserving) 'PrimView' from an arbitrary value.
--
-- @
-- 'like' a '.' 'like' b ≡ 'like' b
-- a '^.' 'like' b ≡ b
-- a '^.' 'like' b ≡ a '^.' 'to' ('const' b)
-- @
--
-- This can be useful as a second case 'failing' a 'Fold'
-- e.g. @foo `failing` 'like' 0@
--
like :: a -> PrimView s t a b
like = to . const
{-# INLINE like #-}

-- | Obtain a constant-valued (index-preserving) 'PrimReview' from an arbitrary value.
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

---------------------------------------------------------------------
-- Derived operators
---------------------------------------------------------------------

-- | View the value pointed to by a 'View', 'Data.Profunctor.Optic.Iso.Iso' or
-- 'Lens' or the result of folding over all the results of a
-- 'Data.Profunctor.Optic.Fold.Fold' or 'Data.Profunctor.Optic.Traversal.Traversal' that points
-- at a monoidal value.
--
-- @
-- 'view' '.' 'to' ≡ 'id'
-- @
--
-- >>> view second (1, "hello")
-- "hello"
--
-- >>> view (to succ) 5
-- 6
--
-- >>> view (second . first) ("hello",("world","!!!"))
-- "world"
--
view :: MonadReader s m => AView s a -> m a
view o = views o id
{-# INLINE view #-}

-- | Turn an optic around and look through the other end.
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
-- 'review' :: 'Relens'' s a -> a -> s
-- @
--
review :: MonadReader b m => AReview t b -> m t
review p = asks (unTagged #. p .# Tagged)
{-# INLINE review #-}

infixl 8 ^.

-- | An infix alias for 'view'. Dual to '#'.
--
-- The fixity and semantics are such that subsequent field accesses can be
-- performed with ('Prelude..').
--
-- >>> ("hello","world") ^. second
-- "world"
--
-- >>> import Data.Complex
-- >>> ((0, 1 :+ 2), 3) ^. first . second . to magnitude
-- 2.23606797749979
--
-- @
-- ('^.') ::             s -> 'View' s a     -> a
-- ('^.') :: 'Data.Monoid.Monoid' m => s -> 'Data.Profunctor.Optic.Fold.Fold' s m       -> m
-- ('^.') ::             s -> 'Data.Profunctor.Optic.Iso.Iso'' s a       -> a
-- ('^.') ::             s -> 'Data.Profunctor.Optic.Lens.Lens'' s a      -> a
-- ('^.') ::             s -> 'Data.Profunctor.Optic.Prism.Reprism'' s a      -> a
-- ('^.') :: 'Data.Monoid.Monoid' m => s -> 'Data.Profunctor.Optic.Traversal.Traversal'' s m -> m
-- @
--
(^.) :: s -> AView s a -> a
(^.) = flip view
{-# INLINE ( ^. ) #-}

infixr 8 #

-- | An infix alias for 'review'. Dual to '^.'.
--
-- @
-- 'from' f # x ≡ f x
-- l # x ≡ x '^.' 're' l
-- @
--
-- This is commonly used when using a 'Prism' as a smart constructor.
--
-- >>> left # 4
-- Left 4
--
-- @
-- (#) :: 'Iso''      s a -> a -> s
-- (#) :: 'Prism''    s a -> a -> s
-- (#) :: 'Relens''   s a -> a -> s
-- (#) :: 'Review'    s a -> a -> s
-- (#) :: 'Equality'' s a -> a -> s
-- @
--
(#) :: AReview t b -> b -> t
o # b = review o b
{-# INLINE ( # ) #-}

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

---------------------------------------------------------------------
-- 'MonadState' and 'MonadWriter'
---------------------------------------------------------------------

-- | TODO: Document
--
use :: MonadState s m => AView s a -> m a
use o = gets (view o)
{-# INLINE use #-}

-- | Turn an optic around and 'use' a value (or the current environment) through it the other way.
--
-- @
-- 'reuse' ≡ 'use' '.' 're'
-- 'reuse' '.' 'from' ≡ 'gets'
-- @
--
-- >>> evalState (reuse left) 5
-- Left 5
--
-- >>> evalState (reuse (from succ)) 5
-- 6
--
-- @
-- 'reuse' :: 'MonadState' a m => 'Iso'' s a   -> m s
-- 'reuse' :: 'MonadState' a m => 'Prism'' s a -> m s
-- 'reuse' :: 'MonadState' a m => 'Relens'' s a -> m s
-- @
--
reuse :: MonadState b m => AReview t b -> m t
reuse p = gets (unTagged #. p .# Tagged)
{-# INLINE reuse #-}

-- | Use the target of a 'Lens', 'Data.Profunctor.Optic.Iso.Iso' or
-- 'View' in the current state, or use a summary of a
-- 'Data.Profunctor.Optic.Fold.Fold' or 'Data.Profunctor.Optic.Traversal.Traversal' that
-- points to a monoidal value.
--
-- >>> evalState (uses first length) ("hello","world")
-- 5
--
-- @
-- 'uses' :: 'MonadState' s m             => 'Data.Profunctor.Optic.Iso.Iso'' s a       -> (a -> r) -> m r
-- 'uses' :: 'MonadState' s m             => 'Data.Profunctor.Optic.View.View' s a     -> (a -> r) -> m r
-- 'uses' :: 'MonadState' s m             => 'Data.Profunctor.Optic.Lens.Lens'' s a      -> (a -> r) -> m r
-- 'uses' :: 'MonadState' s m             => 'Data.Profunctor.Optic.Prism.Reprism'' s a      -> (a -> r) -> m r
-- 'uses' :: 'MonadState' s m => 'Data.Monoid.Monoid' r => 'Data.Profunctor.Optic.Traversal.Traversal'' s a -> (a -> r) -> m r
-- 'uses' :: 'MonadState' s m => 'Data.Monoid.Monoid' r => 'Data.Profunctor.Optic.Fold.Fold' s a       -> (a -> r) -> m r
-- @
--
-- @
-- 'uses' :: 'MonadState' s m => 'Getting' r s t a b -> (a -> r) -> m r
-- @
--
uses :: MonadState s m => Optic' (FoldRep r) s a -> (a -> r) -> m r
uses l f = gets (views l f)
{-# INLINE uses #-}

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
-- @
-- 'reuses' :: 'MonadState' a m => 'Iso'' s a   -> (s -> r) -> m r
-- 'reuses' :: 'MonadState' a m => 'Prism'' s a -> (s -> r) -> m r
-- 'reuses' :: 'MonadState' a m => 'Prism'' s a -> (s -> r) -> m r
-- @
--
reuses :: MonadState b m => AReview t b -> (t -> r) -> m r
reuses p tr = gets (tr . unTagged #. p .# Tagged)
{-# INLINE reuses #-}

-- | Extracts the portion of a log that is focused on by a 'View'. 
--
-- Given a 'Fold' or a 'Traversal', then a monoidal summary of the parts 
-- of the log that are visited will be returned.
--
-- @
-- 'listening' :: 'MonadWriter' w m             => 'Iso'' w u       -> m a -> m (a, u)
-- 'listening' :: 'MonadWriter' w m             => 'Lens'' w u      -> m a -> m (a, u)
-- 'listening' :: 'MonadWriter' w m             => 'View' w u     -> m a -> m (a, u)
-- 'listening' :: 'MonadWriter' w m => 'Monoid' u => 'Fold' w u       -> m a -> m (a, u)
-- 'listening' :: 'MonadWriter' w m => 'Monoid' u => 'Traversal'' w u -> m a -> m (a, u)
-- 'listening' :: 'MonadWriter' w m => 'Monoid' u => 'Prism'' w u     -> m a -> m (a, u)
-- @
--
listening :: MonadWriter w m => AView w u -> m a -> m (a, u)
listening l m = do
  (a, w) <- Writer.listen m
  return (a, view l w)
{-# INLINE listening #-}

-- | TODO: Document
--
listenings :: MonadWriter w m => Optic' (FoldRep v) w u -> (u -> v) -> m a -> m (a, v)
listenings l uv m = do
  (a, w) <- listen m
  return (a, views l uv w)
{-# INLINE listenings #-}

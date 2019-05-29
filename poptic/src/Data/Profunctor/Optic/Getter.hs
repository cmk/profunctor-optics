{-# LANGUAGE TypeOperators    #-}

module Data.Profunctor.Optic.Getter where

import Control.Arrow ((&&&))
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Operator
import Data.Profunctor.Optic.Prelude (Const(..), lmap)
import Data.Profunctor.Optic.Prism (_Just)
import Control.Monad.Reader as Reader
import Control.Monad.Writer as Writer
import Control.Monad.State as State


---------------------------------------------------------------------
-- 'Getter'
---------------------------------------------------------------------

-- laws 
-- getter_complete :: Getter s a -> Bool
-- getter_complete o = tripping o $ to (view o)

-- | Build a 'Getter' from an arbitrary function.
--
-- @
-- 'to' f '.' 'to' g ≡ 'to' (g '.' f)
-- @
--
-- @
-- a '^.' 'to' f ≡ f a
-- @
--
-- @
-- 'to' f ≡ dimap f (contramap f)
-- @
--
-- >>> a ^. to f
-- f a
--
-- >>> view ("hello","world") ^. to snd
-- "world"
--
-- >>> 5^.to succ
-- 6
--
-- >>> (0, -5) ^. _2 . to abs
-- 5
--
-- @
-- 'to' :: (s -> a) -> 'Getter' s a
-- @
--
to :: (s -> a) -> PrimGetter s t a b
to f = ocoerce . lmap f
{-# INLINE to #-}


--to' :: (Profunctor p, Contravariant f) => (s -> a) -> p a (f a) -> p s (f s)
--to' k = dimap k (contramap k)
-- ocoerce (Star h) = Star $ coerce . h


-- | Build a constant-valued (index-preserving) 'PrimGetter' from an arbitrary value.
--
-- @
-- 'like' a '.' 'like' b ≡ 'like' b
-- a '^.' 'like' b ≡ b
-- a '^.' 'like' b ≡ a '^.' 'to' ('const' b)
-- @
--
-- This can be useful as a second case 'failing' a 'Fold'
-- e.g. @foo `failing` 'like' 0@
like :: a -> PrimGetter s t a b
like a = to (const a)


-- @
-- 'cloneGetter' :: 'Getting' a s a -> 'Getter' s a
-- @
cloneGetter :: Getting a s a -> PrimGetter s t a b
cloneGetter = to . view

-- @
-- 'cloneGetter' :: 'Getting' a s a -> 'Getting' b s b -> 'Getter' s (a, b)
-- @
cloneGetters :: Getting a s a -> Getting b s b -> PrimGetter' s (a, b)
cloneGetters l r = to (view l &&& view r)



---------------------------------------------------------------------
-- Derived operators
---------------------------------------------------------------------

infixl 8 ^.
(^.) :: s -> Getting a s a -> a
(^.) = flip view


-- ^ @
-- 'view o ≡ foldMapOf o id'
-- @
view :: MonadReader s m => Getting a s a -> m a
view = Reader.asks . (`foldMapOf` id)
{-# INLINE view #-}


-- ^ @
-- 'views o f ≡ foldMapOf o f'
-- @
views :: MonadReader s m => Getting r s a -> (a -> r) -> m r
views o f = Reader.asks $ foldMapOf o f
{-# INLINE views #-}


use :: MonadState s m => Getting a s a -> m a
use o = State.gets (view o)


-- | Extracts the portion of a log that is focused on by a 'Getter'. 
--
-- Given a 'Fold' or a 'Traversal', then a monoidal summary of the parts 
-- of the log that are visited will be returned.
--
-- @
-- 'listening' :: 'MonadWriter' w m             => 'Getter' w u     -> m a -> m (a, u)
-- 'listening' :: 'MonadWriter' w m             => 'Lens'' w u      -> m a -> m (a, u)
-- 'listening' :: 'MonadWriter' w m             => 'Iso'' w u       -> m a -> m (a, u)
-- 'listening' :: ('MonadWriter' w m, 'Monoid' u) => 'Fold' w u       -> m a -> m (a, u)
-- 'listening' :: ('MonadWriter' w m, 'Monoid' u) => 'Traversal'' w u -> m a -> m (a, u)
-- 'listening' :: ('MonadWriter' w m, 'Monoid' u) => 'Prism'' w u     -> m a -> m (a, u)
-- @
listening :: MonadWriter w m => Getting u w u -> m a -> m (a, u)
listening l m = do
  (a, w) <- Writer.listen m
  return (a, view l w)
{-# INLINE listening #-}

listenings :: MonadWriter w m => Getting v w u -> (u -> v) -> m a -> m (a, v)
listenings l uv m = do
  (a, w) <- listen m
  return (a, views l uv w)
{-# INLINE listenings #-}

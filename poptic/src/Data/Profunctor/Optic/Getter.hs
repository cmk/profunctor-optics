module Data.Profunctor.Optic.Getter where

import Control.Arrow ((&&&))
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Operators
import Data.Profunctor.Optic.Prism (_Just)
import Control.Monad.Writer as Writer
import Control.Monad.State as State
-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> import Data.Profunctor.Optic.Type 
-- >>> import Debug.SimpleReflect.Expr
-- >>> import Debug.SimpleReflect.Vars as Vars hiding (f,g)
-- >>> let f :: Expr -> Expr; f = Debug.SimpleReflect.Vars.f
-- >>> let g :: Expr -> Expr; g = Debug.SimpleReflect.Vars.g


---------------------------------------------------------------------
-- Getter
---------------------------------------------------------------------


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
to :: (s -> a) -> PrimGetter s a
to f = ocoerce . lmap f
{-# INLINE to #-}

--to' :: (Profunctor p, Contravariant f) => (s -> a) -> p a (f a) -> p s (f s)
--to' k = dimap k (contramap k)
-- ocoerce (Star h) = Star $ coerce . h

{-
getPreview :: Optic (Star (Pre a)) s t a b -> PrimGetter s s (Maybe a) (Maybe a)
getPreview = to . preview
{-# INLINE getPreview  #-}
-}


-- | Build an constant-valued (index-preserving) 'Getter' from an arbitrary value.
--
-- @
-- 'like' a '.' 'like' b ≡ 'like' b
-- a '^.' 'like' b ≡ b
-- a '^.' 'like' b ≡ a '^.' 'to' ('const' b)
-- @
--
-- This can be usefusl as a second case 'failing' a 'Fold'
-- e.g. @foo `failing` 'like' 0@
like :: a -> PrimGetter s a
like a = to (const a)


takeBoth :: AGetter a s a -> AGetter a' s a' -> Getter s (a, a')
takeBoth l r = to (view l &&& view r)


-- | We can freely convert a 'Getter s (Maybe a)' into an 'AffineFold s a'.
-- getJust :: Getting (Maybe a) s (Maybe a) -> AffineFold s a
getJust :: Choice p => (p (Maybe a) (Maybe b) -> c) -> p a b -> c
getJust o = o . _Just


---------------------------------------------------------------------
-- Derived operators
---------------------------------------------------------------------

infixl 8 ^.
(^.) :: s -> AGetter a s a -> a
(^.) s o = foldMapOf o id s

use :: MonadState s m => AGetter a s a -> m a
use l = State.gets (view l)



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
listening :: MonadWriter w m => AGetter u w u -> m a -> m (a, u)
listening l m = do
  (a, w) <- Writer.listen m
  return (a, view l w)
{-# INLINE listening #-}

listenings :: MonadWriter w m => AGetter v w u -> (u -> v) -> m a -> m (a, v)
listenings l uv m = do
  (a, w) <- listen m
  return (a, views l uv w)
{-# INLINE listenings #-}

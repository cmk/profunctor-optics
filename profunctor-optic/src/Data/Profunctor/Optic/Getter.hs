module Data.Profunctor.Optic.Getter where

import Control.Arrow ((&&&))
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Operators
import Data.Profunctor.Optic.Prism (_Just)


-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> import Data.Profunctor.Optic.Types 
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
to :: (s -> a) -> PrimGetter s s a a
to f = cimap f f
{-# INLINE to #-}


-- | A variant of 'to' for a fully polymorphic 'PrimGetter'.
primgetting :: (s -> a) -> (t -> b) -> PrimGetter s t a b
primgetting = cimap
{-# INLINE primgetting #-}


getPreview :: Optic (Previewed a) s t a b -> PrimGetter s s (Maybe a) (Maybe a)
getPreview = to . preview
{-# INLINE getPreview  #-}



-- | Build an constant-valued (index-preserving) 'Getter' from an arbitrary value.
--
-- @
-- 'like' a '.' 'like' b ≡ 'like' b
-- a '^.' 'like' b ≡ b
-- a '^.' 'like' b ≡ a '^.' 'to' ('const' b)
-- @
--
-- This can be useful as a second case 'failing' a 'Fold'
-- e.g. @foo `failing` 'like' 0@
like :: a -> PrimGetter s s a a
like a = to (const a)


takeBoth 
  :: Optic (Forget c) s t c b
  -> Optic (Forget d) s t d b 
  -> Getter s (c, d)
takeBoth l r = to (view l &&& view r)


-- | We can freely convert a 'Getter s (Maybe a)' into an 'AffineFold s a'.
getJust :: Getter s (Maybe a) -> AffineFold s a
getJust o = o . _Just


---------------------------------------------------------------------
-- Derived operators
---------------------------------------------------------------------

infixl 8 ^.
(^.) :: s -> Optic (Forget a) s t a b -> a
(^.) = flip view

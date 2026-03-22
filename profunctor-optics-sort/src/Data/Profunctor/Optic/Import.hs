-- | Re-exports from profunctor-optics plus indexed dual optic types.
--
-- Most Relens/Reprism functionality is now in profunctor-optics core.
-- This module re-exports the core and adds indexed variants that
-- have not yet been promoted.
module Data.Profunctor.Optic.Import
  ( -- * Re-exports from profunctor-optics
    module Data.Profunctor.Optic

    -- * Indexed dual optic types (not yet in core)
  , Rxlens, Rxlens'
  , Ixprism, Ixprism'
  , Rxprism, Rxprism'

    -- * Indexed dual constructors
  , rlens, rlensVl
  , jprism, iprism, iprism', jprism'
  , rprism, rprism'

    -- * Indexed dual stock optics
  , rfirst, rsecond
  ) where

import Data.Bifunctor as B (Bifunctor(..), second)

import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Iso
import Data.Profunctor.Optic.Lens
import Data.Profunctor.Optic.Prism
import Data.Profunctor.Optic.Setter
import Data.Profunctor.Optic.View
import Data.Profunctor.Optic.Fold
import Data.Profunctor.Optic.Traversal
import Data.Profunctor.Optic.Combinator
import Data.Profunctor.Optic.Types

-- ---------------------------------------------------------------------------
-- Indexed dual optic types

-- | Indexed relens: coindexed by @r@.
type Rxlens r s t a b = forall p. Costrong p => Ixoptic p r s t a b
type Rxlens' r s a = Rxlens r s s a a

-- | Indexed prism.
type Ixprism i s t a b = forall p. Choice p => Ixoptic p i s t a b
type Ixprism' i s a = Ixprism i s s a a

-- | Indexed reprism: coindexed by @r@.
type Rxprism r s t a b = forall p. Cochoice p => Ixoptic p r s t a b
type Rxprism' r s a = Rxprism r s s a a

-- ---------------------------------------------------------------------------
-- Indexed dual constructors

-- | Indexed 'Relens'.
rlens :: (b -> s -> (r, a)) -> (b -> t) -> Rxlens r s t a b
rlens bsia bt = rlensVl $ \ts b -> bsia b <$> (ts . bt $ b)
{-# INLINE rlens #-}

-- | Van Laarhoven indexed relens.
rlensVl :: (forall f. Functor f => (t -> f s) -> b -> f (r, a)) -> Rxlens r s t a b
rlensVl f = relensVl $ \ts -> f (fmap snd . ts)
{-# INLINE rlensVl #-}

-- | Indexed 'Prism' from an indexed matcher.
jprism :: (i -> s -> Either t a) -> (b -> t) -> Ixprism i s t a b
jprism ista bt = prism (\(i,s) -> fmap (i,) (ista i s)) bt

-- | Indexed 'Prism' from a matcher that returns an indexed result.
iprism :: (s -> Either t (i, a)) -> (b -> t) -> Ixprism i s t a b
iprism stia bt = prism (stia . snd) bt

-- | Indexed 'Prism'' from a 'Maybe' matcher.
iprism' :: (s -> Maybe (i, a)) -> (a -> s) -> Ixprism' i s a
iprism' sia as = iprism (\s -> maybe (Left s) Right (sia s)) as

-- | Indexed 'Prism'' from an indexed 'Maybe' matcher.
jprism' :: (i -> s -> Maybe a) -> (a -> s) -> Ixprism' i s a
jprism' isa as = prism (\(i,s) -> maybe (Left s) (Right . (i,)) (isa i s)) as

-- | Indexed 'Reprism'.
rprism :: Monoid r => (r -> s -> a) -> (b -> Either a t) -> Rxprism r s t a b
rprism rsa bat = reprism (fanout (const mempty) (uncurry rsa)) (B.first (mempty,) . bat)

-- | Indexed 'Reprism'' from a 'Maybe' matcher.
rprism' :: Monoid r => (r -> s -> a) -> (a -> Maybe s) -> Rxprism' r s a
rprism' rsa ams = rprism rsa $ \b -> maybe (Left b) Right (ams b)

-- ---------------------------------------------------------------------------
-- Indexed dual stock optics

-- | Indexed @Relens@ into the first component.
rfirst :: Rxlens r a b (a, c) (b, c)
rfirst = unfirst . lmap assocr

-- | Indexed @Relens@ into the second component.
rsecond :: Rxlens r a b (c, a) (c, b)
rsecond = unsecond . lmap (\(c, (r, a)) -> (r, (c, a)))

-- ---------------------------------------------------------------------------
-- Helpers (re-exported from core Import)

assocr :: ((a, b), c) -> (a, (b, c))
assocr ((a, b), c) = (a, (b, c))
{-# INLINE assocr #-}

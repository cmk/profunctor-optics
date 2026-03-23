-- | Re-exports from profunctor-optics plus indexed dual constructors.
--
-- Most Relens/Reprism types are now in profunctor-optics core.
-- This module re-exports the core and adds indexed constructors
-- that have not yet been promoted.
module Data.Profunctor.Optic.Import
  ( -- * Re-exports from profunctor-optics
    module Data.Profunctor.Optic

    -- * Indexed dual constructors
  , rlens, rlensVl
  , jprism, iprism, iprism', jprism'
  , rprism, rprism'

    -- * Indexed dual stock optics
  , rfirst, rsecond
  ) where

import Data.Bifunctor as B (Bifunctor(..), first)

import Data.Profunctor.Optic

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
rprism rsa bat = reprism (\(r,s) -> (mempty, rsa r s)) (B.first (mempty,) . bat)

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
-- Helpers

assocr :: ((a, b), c) -> (a, (b, c))
assocr ((a, b), c) = (a, (b, c))
{-# INLINE assocr #-}

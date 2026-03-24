{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Two duality combinators for profunctor optics.
--
-- Profunctor optics have two independent axes of duality:
--
-- == Re — Strong\/Costrong parameter-flip duality
--
-- 'Re' reverses an optic by flipping the parameters of the profunctor.
-- It works because certain profunctor classes come in symmetric pairs:
-- 'Strong' \(\leftrightarrow\) 'Costrong', 'Choice' \(\leftrightarrow\)
-- 'Cochoice', 'Bifunctor' \(\leftrightarrow\) 'Contravariant'. Each
-- pair has an introduction and an elimination form (@first'@ \/ @unfirst@,
-- @right'@ \/ @unright@) and 'Re' routes one to the other.
--
-- @
-- 're' :: 'Lens' s t a b   -> 'Relens' b a t s
-- 're' :: 'Prism' s t a b  -> 'Reprism' b a t s
-- 're' :: 'View' s a       -> 'Review' a s
-- @
--
-- 'Re' is involutive: @'re' . 're' ≡ id@.
--
-- == Co — Star\/Costar structural duality
--
-- The Star\/Costar duality relates optics that work through covariant
-- functors (@Star f@: @a -> f b@) to those that work through
-- contravariant extraction (@Costar f@: @f a -> b@). At the type level
-- this is the relationship between 'Strong' and 'Closed', and between
-- 'Lens' and 'Colens', 'Traversal' and 'Cotraversal', 'View' and
-- 'Coview', etc.
--
-- Unlike 'Re', this duality /cannot/ be witnessed by a simple parameter
-- flip. The fundamental asymmetry is:
--
--   * Products have projections: @fst :: (a, c) -> a@, enabling
--     @unfirst :: p (a, c) (b, c) -> p a b@.
--   * Exponentials do not: there is no general
--     @unclosed :: p (x -> a) (x -> b) -> p a b@ because you cannot
--     extract @a@ from @x -> a@ without an @x@.
--
-- 'Co' is defined as the free 'Closed' construction: given any
-- profunctor @p@, @Co p@ is 'Closed'. Unlike 'Re', 'Co' is /not/
-- involutive — @'co' . 'co'@ does not recover the original optic.
-- It freely adjoins 'Closed' structure, which means it can transform
-- a 'Lens' into a 'Colens'-compatible optic, but the round-trip
-- loses the original 'Strong' structure.
--
-- 'Co' does preserve 'Sieve' and 'Cosieve' structure from the
-- underlying profunctor (with appropriate constraints on the
-- functor), and inherits 'Representable' and 'Corepresentable'
-- when the representation functor is 'Distributive' or 'Functor'
-- respectively.
--
-- == Ix\/Cx duality
--
-- At the index level, 'Ix' @p k a b = p (k, a) b@ threads the
-- index as a product on the left, while 'Cx' @p k a b = p a (k -> b)@
-- threads it as a function on the right. These are related by
-- currying\/uncurrying:
--
--   * 'ixCx' curries the index (@Ix → Cx@), requiring 'Closed' + 'Strong'
--   * 'cxIx' uncurries the coindex (@Cx → Ix@), requiring 'Strong' + 'Closed'
--
-- Both directions require /both/ constraints, because the optic must
-- convert in one direction for the input and the other for the output.
-- This limits 'cxIx' and 'ixCx' to 'Iso'-like optics in practice.
--
-- == Connection to free constructions and representation functors
--
-- The Ix\/Cx duality connects to 'Re' and 'Co' through the free
-- profunctor constructions. Self-coindexing (@'Cx'' p a b = p a (a -> b)@)
-- is isomorphic to the free 'Strong' construction (@Pastro p a b@),
-- witnessed by 'cxpastro' in "Data.Profunctor.Optic.Combinator".
-- Meanwhile, 'Co' is the free 'Closed' construction (isomorphic to
-- @Environment p@ from @profunctors@).
--
-- @
-- 'Cx'' p  ≅  Pastro p       (free 'Strong')
-- 'Co'  p  ≅  Environment p  (free 'Closed')
-- @
--
-- At the representation level, the same duality appears in the
-- 'Index' and 'Coindex' types (see "Data.Profunctor.Optic.Carrier"):
--
-- @
-- 'Index'   a b s = (a, b -> s)       — 'Rep' of 'LensRep' (Strong\/Star side)
-- 'Coindex' a b s = (s -> b) -> a     — 'Corep' of 'ColensRep' (Closed\/Costar side)
-- @
--
-- 'Index' @a a@ is 'Coapplicative' (lives on the 'Costar' side), while
-- 'Coindex' @a a@ is 'Applicative' (lives on the 'Star' side). The
-- parameter swap between them (@'LensRep' a b@ sieves to @'Index' a b@,
-- @'ColensRep' a b@ cosieves to @'Coindex' b a@) mirrors the flip
-- performed by 'Re'.
--
-- == Summary
--
-- @
--             'Re'                    'Co'
-- Witnesses   Strong ↔ Costrong     Strong → Closed
--             Choice ↔ Cochoice     (one direction only)
-- Involutive  yes                   no
-- Use         're' :: Lens → Relens  'co' :: Lens → Colens
--             (parameter flip)       (structural transform)
-- @
--
-- @
--             'cxIx'                    'ixCx'
-- Direction   Cx → Ix (uncurry)        Ix → Cx (curry)
-- Requires    Strong + Closed          Strong + Closed
-- @
--
-- See also "Data.Profunctor.Optic.View" for how this affects the
-- 'review' \/ 'cxview' operator surface.
module Data.Profunctor.Optic.Dual (
    -- * Re
    Re(..), re
    -- * Co
  , Co(..), co, liftCo, lowerCo
    -- * Ix\/Cx duality
  , cxIx, ixCx
    -- * Utilities
  , between
) where

import Data.Bifunctor (Bifunctor(..))
import Data.Profunctor.Optic.Import

-- Defined here to avoid circular dependency with Types.hs.
type Optic p s t a b = p a b -> p s t

---------------------------------------------------------------------
-- Re
---------------------------------------------------------------------

-- | 'Re' witnesses the symmetry between the parameters of a 'Profunctor'.
--
-- 'Re' can reverse optics built from classes that have a mirror image:
--
--   * 'Strong' \(\leftrightarrow\) 'Costrong'
--   * 'Choice' \(\leftrightarrow\) 'Cochoice'
--   * 'Bifunctor' \(\leftrightarrow\) 'Contravariant'
--
-- 'Re' cannot reverse 'Closed', 'Representable', or 'Corepresentable'
-- because these classes have no standard dual. A hypothetical @Coclosed@
-- with @unclosed :: p (x -> a) (x -> b) -> p a b@ would enable
-- @Closed p => Coclosed (Re p)@, but no such class exists in the
-- profunctor hierarchy. Consequently, 'Colens', 'Cotraversal', and
-- other 'Closed'-based optics cannot be reversed with 're'.
--
-- See 'Co' for the Star\/Costar duality axis, which handles
-- the 'Closed' side.
--
newtype Re p s t a b = Re { runRe :: p b a -> p t s }

instance Profunctor p => Profunctor (Re p s t) where
  dimap f g (Re p) = Re (p . dimap g f)

instance Strong p => Costrong (Re p s t) where
  unfirst (Re p) = Re (p . first')

instance Costrong p => Strong (Re p s t) where
  first' (Re p) = Re (p . unfirst)

instance Choice p => Cochoice (Re p s t) where
  unright (Re p) = Re (p . right')

instance Cochoice p => Choice (Re p s t) where
  right' (Re p) = Re (p . unright)

instance Profunctor p => Functor (Re p s t a) where
  fmap f (Re p) = Re (p . lmap f)

instance (Profunctor p, forall x. Contravariant (p x)) => Bifunctor (Re p s t) where
  first f (Re p) = Re (p . contramap f)

  second f (Re p) = Re (p . lmap f)

instance Bifunctor p => Contravariant (Re p s t a) where
  contramap f (Re p) = Re (p . first f)

-- | Reverse an optic to obtain its 'Re'-dual (Strong\/Costrong
-- parameter-flip duality).
--
-- @
-- 're' . 're'  ≡ id
-- @
--
-- 're' swaps 'Strong' \(\leftrightarrow\) 'Costrong' and 'Choice' \(\leftrightarrow\) 'Cochoice':
--
-- @
-- 're' :: 'Iso' s t a b    -> 'Iso' b a t s
-- 're' :: 'Lens' s t a b   -> 'Relens' b a t s
-- 're' :: 'Prism' s t a b  -> 'Reprism' b a t s
-- 're' :: 'View' s a       -> 'Review' a s
-- 're' :: 'Review' t b     -> 'View' b t
-- @
--
-- This is the Strong\/Costrong (parameter-flip) duality. For the
-- Star\/Costar (structural) duality, see 'co'.
--
-- >>> 5 ^. re left'
-- Left 5
--
re :: Optic (Re p a b) s t a b -> Optic p b a t s
re o = (between runRe Re) o id
{-# INLINE re #-}

---------------------------------------------------------------------
-- Co
---------------------------------------------------------------------

-- | 'Co' witnesses the Star\/Costar structural duality by freely
-- adjoining 'Closed' to any profunctor.
--
-- Where 'Re' works by flipping profunctor parameters (a mechanical,
-- involutive operation), 'Co' performs a structural transformation:
-- it takes a profunctor that may be 'Strong' (product-based, like
-- 'Star') and produces one that is 'Closed' (exponential-based, like
-- 'Costar').
--
-- This transformation is /not/ involutive: @'co' . 'co'@ freely
-- adjoins 'Closed' twice, rather than recovering the original optic.
-- The reason is that 'Closed' has no inverse — there is no general
-- @unclosed :: p (x -> a) (x -> b) -> p a b@ — because exponentials
-- lack projections (you cannot extract @a@ from @x -> a@ without
-- an @x@).
--
-- == Instances
--
-- 'Co' is always 'Profunctor' and 'Closed'. Additionally:
--
--   * @'Sieve' p f, 'Distributive' f => 'Sieve' ('Co' p) f@
--   * @'Cosieve' p g, 'Functor' g => 'Cosieve' ('Co' p) g@
--
-- These constraints are not accidental — they are exactly the
-- conditions under which @Star f@ and @Costar g@ are 'Closed'
-- (@'Distributive' f => 'Closed' ('Star' f)@ and
-- @'Functor' g => 'Closed' ('Costar' g)@). 'Co' works by
-- instantiating its universally quantified @r@ at @Star f@ or
-- @Costar g@, so the 'Closed' requirement on @r@ surfaces as
-- these constraints.
--
-- 'Co' cannot be 'Representable' or 'Corepresentable' because
-- these require 'Strong' and 'Costrong' respectively as superclasses,
-- which 'Co' does not provide.
--
newtype Co p a b = Co
  { runCo :: forall r. Closed r => (forall x y. p x y -> r x y) -> r a b }

instance Profunctor (Co p) where
  dimap f g (Co e) = Co $ \k -> dimap f g (e k)
  {-# INLINE dimap #-}

instance Closed (Co p) where
  closed (Co e) = Co $ \k -> closed (e k)
  {-# INLINE closed #-}

instance Profunctor p => Functor (Co p a) where
  fmap f (Co e) = Co $ \k -> rmap f (e k)
  {-# INLINE fmap #-}

instance (Sieve p f, Distributive f) => Sieve (Co p) f where
  sieve (Co e) = sieve (e (\pxy -> Star (sieve pxy)))
  {-# INLINE sieve #-}

instance (Cosieve p g, Functor g) => Cosieve (Co p) g where
  cosieve (Co e) = cosieve (e (\pxy -> Costar (cosieve pxy)))
  {-# INLINE cosieve #-}

-- Note: Representable requires Strong and Corepresentable requires
-- Costrong as superclasses, neither of which Co can provide.
-- Co freely adjoins Closed, but cannot recover Strong or Costrong.

-- | Lift a profunctor value into 'Co', freely adjoining 'Closed'.
--
-- @
-- 'liftCo' :: p a b -> 'Co' p a b
-- @
--
liftCo :: p a b -> Co p a b
liftCo pab = Co $ \k -> k pab
{-# INLINE liftCo #-}

-- | Extract from 'Co' back to the underlying profunctor.
--
-- This requires the underlying profunctor to be 'Closed', because
-- 'Co' may have used 'closed' internally. This is the key asymmetry
-- with 'Re': 'runRe' only needs the identity natural transformation,
-- but 'lowerCo' needs @p@ to support everything 'Co' might have done.
--
lowerCo :: Closed p => Co p a b -> p a b
lowerCo (Co e) = e id
{-# INLINE lowerCo #-}

-- | Transform an optic along the Star\/Costar duality axis.
--
-- @
-- 'co' :: 'Closed' p => 'Optic' ('Co' p) s t a b -> 'Optic' p s t a b
-- @
--
-- Unlike 're', 'co' requires a 'Closed' constraint on @p@ to extract
-- the result. This reflects the fundamental asymmetry: 'Re' is
-- involutive (@'re' . 're' ≡ id@) because 'Strong' \(\leftrightarrow\)
-- 'Costrong' are symmetric, but 'co' is one-directional because
-- 'Closed' has no inverse.
--
-- In practice, 'co' witnesses that any optic built from 'Strong'
-- (Lens, Traversal, View, etc.) can be used in a 'Closed' context,
-- but the resulting optic forgets 'Strong' structure.
--
co :: Closed p => Optic (Co p) s t a b -> Optic p s t a b
co o pab = lowerCo (o (liftCo pab))
{-# INLINE co #-}

---------------------------------------------------------------------
-- Ix\/Cx duality
---------------------------------------------------------------------

-- Duplicated from Types.hs to avoid circular imports.
type Ix p k a b = p (k , a) b
type Cx p k a b = p a (k -> b)
type Ixoptic p k s t a b = Ix p k a b -> Ix p k s t
type Cxoptic p k s t a b = Cx p k a b -> Cx p k s t

-- | Convert a coindexed optic to an indexed optic by uncurrying
-- the coindex.
--
-- @
-- 'Cx' p k a b  =  p a (k -> b)     — function coindex on the right
-- 'Ix' p k a b  =  p (k, a) b       — product index on the left
-- @
--
-- Requires both 'Closed' (to curry the input) and 'Strong' (to
-- uncurry the output). This means 'cxIx' and 'ixCx' are only
-- usable with optics that are both 'Strong' and 'Closed' (e.g.
-- 'Iso'), reflecting the fact that currying and uncurrying are
-- inverse operations that each require one half of the duality.
--
cxIx :: (Closed p, Strong p) => Cxoptic p k s t a b -> Ixoptic p k s t a b
cxIx o pka_b =
  let pa_kb   = lmap (\a k -> (k, a)) (closed pka_b)   -- p (k,a) b  →  p a (k->b)
      ps_kt   = o pa_kb                                  -- p a (k->b) →  p s (k->t)
      psk_ktk = first' ps_kt                             -- p s (k->t) →  p (s,k) (k->t, k)
  in  dimap swap (\(f, k) -> f k) psk_ktk                -- p (s,k) (k->t, k) →  p (k,s) t
{-# INLINE cxIx #-}

-- | Convert an indexed optic to a coindexed optic by currying
-- the index.
--
-- @
-- 'ixCx' :: ('Closed' p, 'Strong' p) => 'Ixoptic' p k s t a b -> 'Cxoptic' p k s t a b
-- @
--
-- 'ixCx' requires 'Closed' on @p@ to introduce the function space
-- @(k -> b)@ from the product @(k, a)@, and 'Strong' for the
-- reverse direction on the input. These are the Ix\/Cx analogues
-- of 'co' and 're' at the index level — currying and uncurrying
-- move the index between a product on the left and a function on
-- the right.
--
-- Note: both 'cxIx' and 'ixCx' require /both/ 'Strong' and 'Closed',
-- because each must convert in both directions (once for the input,
-- once for the output of the optic). This means they are only usable
-- with optics that are both 'Strong' and 'Closed' — i.e., 'Iso'-like
-- optics. This is a genuine limitation: you cannot curry an 'Ixlens'
-- into a 'Cxlens' because 'Ixlens' requires 'Strong' but not 'Closed'.
--
ixCx :: (Closed p, Strong p) => Ixoptic p k s t a b -> Cxoptic p k s t a b
ixCx o pa_kb =
  let pka_b   = dimap swap (\(f, k) -> f k) (first' pa_kb)  -- p a (k->b)  →  p (k,a) b
      pks_t   = o pka_b                                       -- p (k,a) b   →  p (k,s) t
      ps_kt   = lmap (\s k -> (k, s)) (closed pks_t)          -- p (k,s) t   →  p s (k->t)
  in  ps_kt
{-# INLINE ixCx #-}

---------------------------------------------------------------------
-- Utilities
---------------------------------------------------------------------

-- | Can be used to rewrite
--
-- > \g -> f . g . h
--
-- to
--
-- > between f h
--
between :: (c -> d) -> (a -> b) -> (b -> c) -> a -> d
between f g = (f .) . (. g)
{-# INLINE between #-}

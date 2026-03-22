{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

#ifndef MIN_VERSION_profunctors
#define MIN_VERSION_profunctors(x,y,z) 1
#endif

module Data.Profunctor.Optic.Types (
    Optic, Optic'
    -- * Optics
    -- ** Ixoptic
  , Ixoptic, Ixoptic'
  , Ix, Ix'
    -- * Equality
  , Equality, Equality'
    -- * Iso,
  , Iso, Iso'
    -- ** Lens, Ixlens
  , Lens, Lens'
  , Ixlens, Ixlens'
    -- ** Prism
  , Prism, Prism'
    -- ** Traversal, Ixtraversal
  , Traversal, Traversal'
  , Ixtraversal, Ixtraversal'
    -- ** Traversal0, Ixtraversal0
  , Traversal0, Traversal0'
  , Ixtraversal0, Ixtraversal0'
    -- ** Traversal1, Ixtraversal1
  , Traversal1, Traversal1'
  , Ixtraversal1, Ixtraversal1'
    -- ** Fold, Ixfold
  , Fold, Ixfold
    -- ** Fold0, Ixfold0
  , Fold0, Ixfold0
    -- ** Fold1, Ixfold1
  , Fold1, Ixfold1
    -- ** View, Ixview
  , View, Ixview
    -- ** Setter, Ixsetter
  , Setter, Setter'
  , Ixsetter, Ixsetter'
    -- ** Setter1, Ixsetter1
  , Setter1, Setter1'
  , Ixsetter1, Ixsetter1'
    -- * Dual Optics
    -- ** Cxoptic
  , Cxoptic, Cxoptic'
  , Cx, Cx'
    -- ** Colens, Cxlens
  , Colens, Colens'
  , Cxlens, Cxlens'
    -- ** Relens, Rxlens
  , Relens, Relens'
  , Rxlens, Rxlens'
    -- ** Reprism
  , Reprism, Reprism'
    -- ** Cotraversal, Cxtraversal
  , Cotraversal, Cotraversal'
  , Cxtraversal, Cxtraversal'
    -- ** Cotraversal0, Cxtraversal0
  , Cotraversal0, Cotraversal0'
  , Cxtraversal0, Cxtraversal0'
    -- ** Cotraversal1, Cxtraversal1
  , Cotraversal1, Cotraversal1'
  , Cxtraversal1, Cxtraversal1'
    -- ** Cofold, Cxfold
  , Cofold, Cxfold
    -- ** Cofold0, Cxfold0
  , Cofold0, Cxfold0
    -- ** Cofold1, Cxfold1
  , Cofold1, Cxfold1
    -- ** Review, Rxview
  , Review, Rxview
    -- ** Cosetter, Cxsetter
  , Cosetter, Cosetter'
  , Cxsetter, Cxsetter'
    -- ** Cosetter1, Cxsetter1
  , Cosetter1, Cosetter1'
  , Cxsetter1, Cxsetter1'
    -- * Constraints
  , Affine, Coaffine
  , Traversing, Cotraversing
  , Traversing1, Cotraversing1
  , Mapping, Remapping
  , Mapping1, Remapping1
  , CoercingL, CoercingR
  , Foldable', Foldable1'
    -- * 'Re'
  , Re(..), re
  , between
  , module Export
) where

import Data.Bifunctor (Bifunctor(..))
import Data.Functor.Apply (Apply(..))
import Data.Profunctor.Optic.Import
import Data.Profunctor.Types as Export

-- $setup
-- >>> :set -XCPP
-- >>> :set -XNoOverloadedStrings
-- >>> :load Data.Profunctor.Optic

---------------------------------------------------------------------
-- Optic
---------------------------------------------------------------------

type Optic p s t a b = p a b -> p s t

type Optic' p s a = Optic p s s a a

type Ixoptic p k s t a b = Ix p k a b -> Ix p k s t

type Ixoptic' p k s a = Ixoptic p k s s a a

type Ix p k a b = p (k , a) b

type Ix' p a b = Ix p a b b

---------------------------------------------------------------------
-- Equality
---------------------------------------------------------------------

-- | \( \mathsf{Equality}\;A = A \cong A \)
--
type Equality s t a b = forall p. Optic p s t a b

type Equality' s a = Equality s s a a

---------------------------------------------------------------------
-- Iso
---------------------------------------------------------------------

-- | \( \mathsf{Iso}\;S\;A = S \cong A \)
--
type Iso s t a b = forall p. Profunctor p => Optic p s t a b

type Iso' s a = Iso s s a a

---------------------------------------------------------------------
-- Lens
---------------------------------------------------------------------

-- | \( \mathsf{Lens}\;S\;A  = \exists C, S \cong C \times A \)
--
type Lens s t a b = forall p. Strong p => Optic p s t a b

type Lens' s a = Lens s s a a

type Ixlens k s t a b = forall p. Strong p => Ixoptic p k s t a b

type Ixlens' k s a = Ixlens k s s a a

---------------------------------------------------------------------
-- Prism
---------------------------------------------------------------------

-- | \( \mathsf{Prism}\;S\;A = \exists D, S \cong D + A \)
--
type Prism s t a b = forall p. Choice p => Optic p s t a b

type Prism' s a = Prism s s a a

---------------------------------------------------------------------
-- Traversal
---------------------------------------------------------------------

-- | \( \mathsf{Traversal}\;S\;A = \exists F : \mathsf{Traversable}, S \equiv F\,A \)
--
type Traversal s t a b = forall p. (Affine p, Traversing p) => Optic p s t a b

type Traversal' s a = Traversal s s a a

type Ixtraversal k s t a b = forall p. (Affine p, Traversing p) => Ixoptic p k s t a b

type Ixtraversal' k s a = Ixtraversal k s s a a

-- | \( \mathsf{Traversal0}\;S\;A = \exists C, D, S \cong D + C \times A \)
--
type Traversal0 s t a b = forall p. Affine p => Optic p s t a b

type Traversal0' s a = Traversal0 s s a a

type Ixtraversal0 k s t a b = forall p. Affine p => Ixoptic p k s t a b

type Ixtraversal0' k s a = Ixtraversal0 k s s a a

-- | \( \mathsf{Traversal1}\;S\;A = \exists F : \mathsf{Traversable1}, S \equiv F\,A \)
--
type Traversal1 s t a b = forall p. (Strong p, Traversing1 p) => Optic p s t a b

type Traversal1' s a = Traversal1 s s a a

type Ixtraversal1 k s t a b = forall p. (Strong p, Traversing1 p) => Ixoptic p k s t a b

type Ixtraversal1' k s a = Ixtraversal1 k s s a a

---------------------------------------------------------------------
-- Fold
---------------------------------------------------------------------

type Fold s a = forall p. (Affine p, Traversing p, CoercingR p) => Optic' p s a

type Ixfold k s a = forall p. (Affine p, Traversing p, CoercingR p) => Ixoptic' p k s a

type Fold0 s a = forall p. (Affine p, CoercingR p) => Optic' p s a

type Ixfold0 k s a = forall p. (Affine p, CoercingR p) => Ixoptic' p k s a

type Fold1 s a = forall p. (Strong p, Traversing1 p, CoercingR p) => Optic' p s a

type Ixfold1 k s a = forall p. (Strong p, Traversing1 p, CoercingR p) => Ixoptic' p k s a

---------------------------------------------------------------------
-- View
---------------------------------------------------------------------

type View s a = forall p. (Strong p, CoercingR p) => Optic' p s a

type Ixview k s a = forall p. (Strong p, CoercingR p) => Ixoptic' p k s a

---------------------------------------------------------------------
-- Setter
---------------------------------------------------------------------

-- | \( \mathsf{Functor}\;S\;A = \exists F : \mathsf{Functor}, S \equiv F\,A \)
--
type Setter s t a b = forall p. (Affine p, Traversing p, Mapping p) => Optic p s t a b

type Setter' s a = Setter s s a a

type Ixsetter k s t a b = forall p. (Affine p, Traversing p, Mapping p) => Ixoptic p k s t a b

type Ixsetter' k s a = Ixsetter k s s a a

type Setter1 s t a b = forall p. (Strong p, Traversing1 p, Mapping1 p) => Optic p s t a b

type Setter1' s a = Setter1 s s a a

type Ixsetter1 k s t a b = forall p. (Strong p, Traversing1 p, Mapping1 p) => Ixoptic p k s t a b

type Ixsetter1' k s a = Ixsetter1 k s s a a

type Cxoptic p k s t a b = Cx p k a b -> Cx p k s t

type Cxoptic' p k t b = Cxoptic p k t t b b

type Cx p k a b = p a (k -> b)

type Cx' p a b = Cx p a a b

-- | \( \mathsf{Colens}\;S\;A = \exists I, S \cong I \to A \)
--
type Colens s t a b = forall p. Closed p => Optic p s t a b

type Colens' s a = Colens s s a a

type Cxlens k s t a b = forall p. Closed p => Cxoptic p k s t a b

type Cxlens' k t b = Cxlens k t t b b

-- | \( \mathsf{Relens}\;S\;A = \exists C, S \cong C \times A \) (Re-reversed)
--
-- The 'Re'-dual of 'Lens'. A 'Relens' is simultaneously a 'View' and a 'Review'.
--
-- @
-- 're' :: 'Lens' s t a b -> 'Relens' b a t s
-- @
--
type Relens s t a b = forall p. Costrong p => Optic p s t a b

type Relens' s a = Relens s s a a

type Rxlens k s t a b = forall p. Costrong p => Ixoptic p k s t a b

type Rxlens' k s a = Rxlens k s s a a

-- | \( \mathsf{Reprism}\;S\;A = \exists D, S \cong D + A \) (Re-reversed)
--
-- The 'Re'-dual of 'Prism'. A 'Reprism' is simultaneously a 'View' and a 'Review'.
--
-- @
-- 're' :: 'Prism' s t a b -> 'Reprism' b a t s
-- @
--
type Reprism s t a b = forall p. Cochoice p => Optic p s t a b

type Reprism' s a = Reprism s s a a

-- | \( \mathsf{Cotraversal}\;S\;A = \exists F : \mathsf{Distributive}, S \equiv F\,A \)
--
type Cotraversal s t a b = forall p. (Coaffine p, Cotraversing p) => Optic p s t a b

type Cotraversal' t b = Cotraversal t t b b

type Cxtraversal k s t a b = forall p. (Coaffine p, Cotraversing p) => Cxoptic p k s t a b

type Cxtraversal' k t b = Cxtraversal k t t b b

-- | \( \mathsf{Cotraversal0}\;S\;A = \exists D, I, S \cong I \to D + A \)
--
type Cotraversal0 s t a b = forall p. Coaffine p => Optic p s t a b

type Cotraversal0' t b = Cotraversal0 t t b b

type Cxtraversal0 k s t a b = forall p. Coaffine p => Cxoptic p k s t a b

type Cxtraversal0' k t b = Cxtraversal0 k t t b b

-- | \( \mathsf{Cotraversal1}\;S\;A = \exists F : \mathsf{Distributive1}, S \equiv F\,A \)
--
type Cotraversal1 s t a b = forall p. (Closed p, Cotraversing1 p) => Optic p s t a b

type Cotraversal1' t b = Cotraversal1 t t b b

type Cxtraversal1 k s t a b = forall p. (Closed p, Cotraversing1 p) => Cxoptic p k s t a b

type Cxtraversal1' k t b = Cxtraversal1 k t t b b

type Cofold t b = forall p. (Affine p, Cotraversing p, CoercingL p) => Optic' p t b

type Cxfold k t b = forall p. (Affine p, Cotraversing p, CoercingL p) => Cxoptic' p k t b

type Cofold0 t b = forall p. (Coaffine p, CoercingL p) => Optic' p t b

type Cxfold0 k t b = forall p. (Coaffine p, CoercingL p) => Cxoptic' p k t b

type Cofold1 t b = forall p. (Choice p, Cotraversing1 p, CoercingL p) => Optic' p t b

type Cxfold1 k t b = forall p. (Choice p, Cotraversing1 p, CoercingL p) => Cxoptic' p k t b

type Review t b = forall p. (Closed p, CoercingL p) => Optic' p t b

type Rxview k t b = forall p. (Closed p, CoercingL p) => Cxoptic' p k t b

-- | \( \quad \mathsf{Cosetter}\;S\;A = \exists n : \mathbb{N}, S \cong \mathsf{Fin}\,n \to A \)
--
-- See also section 3 on Kaleidoscopes < https://cs.ttu.ee/events/nwpt2019/abstracts/paper14.pdf here >.
--
type Cosetter s t a b = forall p. (Coaffine p, Cotraversing p, Remapping p) => Optic p s t a b

type Cosetter' s a = Cosetter s s a a

type Cxsetter k s t a b = forall p. (Coaffine p, Cotraversing p, Remapping p) => Cxoptic p k s t a b

type Cxsetter' k t b = Cxsetter k t t b b

type Cosetter1 s t a b = forall p. (Closed p, Cotraversing1 p, Remapping1 p) => Optic p s t a b

type Cosetter1' s a = Cosetter1 s s a a

type Cxsetter1 k s t a b = forall p. (Closed p, Cotraversing1 p, Remapping1 p) => Cxoptic p k s t a b

type Cxsetter1' k t b = Cxsetter1 k t t b b

---------------------------------------------------------------------
-- Constraints
---------------------------------------------------------------------

type Affine p = (Strong p, Choice p)

type Coaffine p = (Closed p, Choice p)

type Traversing p = (Representable p, Applicative' (Rep p))

type Cotraversing p = (Closed p, Corepresentable p, Coapplicative (Corep p))

type Traversing1 p = (Representable p, Apply (Rep p))

type Cotraversing1 p = (Closed p, Corepresentable p, Coapply (Corep p))

type Mapping p = (Representable p, Distributive (Rep p))

type Remapping p = (Corepresentable p, Traversable (Corep p))

type Mapping1 p = (Representable p, Distributive1 (Rep p))

type Remapping1 p = (Corepresentable p, Traversable1 (Corep p))

type CoercingL p = (Bifunctor p)

type CoercingR p = (forall x. Contravariant (p x))

type Foldable' f = (Functor f, Foldable f)

type Foldable1' f = (Functor f, Foldable1 f)

---------------------------------------------------------------------
-- 'Re'
---------------------------------------------------------------------

-- | The 'Re' type and its instances witness the symmetry between the parameters of a 'Profunctor'.
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

-- | Reverse an optic to obtain its 'Re'-dual.
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
-- Note: this is not the same as the categorical co-dual ('Colens', 'Cotraversal', etc.),
-- which replaces 'Strong' with 'Closed'.
--
-- >>> 5 ^. re left'
-- Left 5
--
re :: Optic (Re p a b) s t a b -> Optic p b a t s
re o = (between runRe Re) o id
{-# INLINE re #-}

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

---------------------------------------------------------------------
-- Orphan instances
---------------------------------------------------------------------

instance Apply f => Apply (Star f a) where
  Star ff <.> Star fx = Star $ \a -> ff a <.> fx a

instance Apply (Costar f a) where
  Costar ff <.> Costar fx = Costar $ \a -> ff a (fx a)

#if !(MIN_VERSION_profunctors(5,4,0))
instance Contravariant f => Contravariant (Star f a) where
  contramap f (Star g) = Star $ contramap f . g
#endif

instance Contravariant f => Bifunctor (Costar f) where
  first f (Costar g) = Costar $ g . contramap f

  second f (Costar g) = Costar $ f . g

#if MIN_VERSION_profunctors(5,4,0)
-- used for Choice operations (e.g. preview) on Cotraversals & Cofolds
-- e.g.
-- distributes left' (1, Left "foo")
instance Coapplicative f => Choice (Costar f) where
  left' (Costar f) = Costar $ either (Left . f) (Right . copure) . coapply
#endif

#if !(MIN_VERSION_profunctors(5,5,0))
instance Cochoice (Forget r) where
  unleft (Forget f) = Forget $ f . Left

  unright (Forget f) = Forget $ f . Right
#endif

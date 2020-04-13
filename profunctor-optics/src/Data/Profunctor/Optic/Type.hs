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

module Data.Profunctor.Optic.Type (
    type (+)
    -- * Optic
  , Optic, Optic'
    -- * Constraints
  , Affine, Coaffine
  , Traversing, Cotraversing
  , Traversing1, Cotraversing1
  , Rescanning, Rescanning1
  , Mapping, Remapping
  , Mapping1, Remapping1
  , CoercingL, CoercingR
  , Traversable, Traversable1
    -- * Equality
  , Equality, Equality'
    -- * Iso
  , Iso, Iso'
    -- * Prism
  , Prism, Prism'
    -- * Lens
  , Lens, Colens
  , Lens', Colens'
    -- * Traversal
  , Traversal0, Cotraversal0
  , Traversal, Cotraversal
  , Traversal1, Cotraversal1
  , Traversal0', Cotraversal0'
  , Traversal', Cotraversal'
  , Traversal1', Cotraversal1'
    -- * Fold
  , Fold0, Cofold0
  , Fold, Cofold
  , Fold1, Cofold1
    -- * Rescan
  , Rescan, Rescan1
  , Rescan', Rescan1'
    -- * Setter
  , Setter, Resetter
  , Setter1, Resetter1
  , Setter', Resetter'
  , Setter1', Resetter1'
    -- * View
  , View, Review
    -- * 'Re'
  , Re(..), re
  , between
  , module Export
) where

import Data.Bifunctor (Bifunctor(..))
import Data.Functor.Apply (Apply(..))
import Data.Profunctor.Optic.Import
import Data.Profunctor.Types as Export
import Data.Foldable (Foldable)
-- $setup
-- >>> :set -XCPP
-- >>> :set -XNoOverloadedStrings
-- >>> :load Data.Profunctor.Optic

type (+) = Either

---------------------------------------------------------------------
-- Constraints
---------------------------------------------------------------------

type Affine p = (Strong p, Choice p)

type Coaffine p = (Closed p, Choice p)

type Traversing p = (Representable p, Applicative' (Rep p))

type Traversing1 p = (Representable p, Apply (Rep p))

type Cotraversing p = (Corepresentable p, Coapply (Corep p))

type Cotraversing1 p = (Corepresentable p, Coapplicative (Corep p))

type Scanning p = (Traversing p, Distributive (Rep p))

type Scanning1 p = (Traversing1 p, Distributive1 (Rep p))

type Rescanning p = (Cotraversing p, Traversable (Corep p))

type Rescanning1 p = (Cotraversing1 p, Traversable1 (Corep p))

type Mapping p = (Scanning p, Monad (Rep p))

type Mapping1 p = (Scanning1 p, Bind (Rep p))

type Remapping p = Rescanning p -- (Rescanning p, Comonad (Corep p))

type Remapping1 p = Rescanning1 p -- (Rescanning1 p, Comonad (Corep p))

type CoercingL p = (Bifunctor p)

type CoercingR p = (forall x. Contravariant (p x))

---------------------------------------------------------------------
-- Optic
---------------------------------------------------------------------

type Optic p s t a b = p a b -> p s t

type Optic' p s a = Optic p s s a a

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
-- Prism
---------------------------------------------------------------------

-- | \( \mathsf{Prism}\;S\;A = \exists D, S \cong D + A \)
--
type Prism s t a b = forall p. Choice p => Optic p s t a b

type Prism' s a = Prism s s a a

---------------------------------------------------------------------
-- Lens
---------------------------------------------------------------------

-- | \( \mathsf{Lens}\;S\;A  = \exists C, S \cong C \times A \)
--
type Lens s t a b = forall p. Strong p => Optic p s t a b

-- | \( \mathsf{Colens}\;S\;A = \exists I, S \cong I \to A \)
--
type Colens s t a b = forall p. Closed p => Optic p s t a b 

type Lens' s a = Lens s s a a

type Colens' s a = Colens s s a a

---------------------------------------------------------------------
-- Traversal
---------------------------------------------------------------------

-- | \( \mathsf{Traversal0}\;S\;A = \exists C, D, S \cong D + C \times A \)
--
type Traversal0 s t a b = forall p. Affine p => Optic p s t a b 

-- | \( \mathsf{Traversal}\;S\;A = \exists F : \mathsf{Traversable}, S \equiv F\,A \)
--
type Traversal s t a b = forall p. (Affine p, Traversing p) => Optic p s t a b

-- | \( \mathsf{Traversal1}\;S\;A = \exists F : \mathsf{Traversable1}, S \equiv F\,A \)
--
type Traversal1 s t a b = forall p. (Strong p, Traversing1 p) => Optic p s t a b 

-- | \( \mathsf{Cotraversal0}\;S\;A = \exists D, I, S \cong I \to D + A \)
--
type Cotraversal0 s t a b = forall p. Coaffine p => Optic p s t a b

-- | \( \mathsf{Cotraversal}\;S\;A = \exists F : \mathsf{Distributive1}, S \equiv F\,A \)
--
type Cotraversal s t a b = forall p. (Coaffine p, Cotraversing p) => Optic p s t a b

-- | \( \mathsf{Cotraversal}\;S\;A = \exists F : \mathsf{Distributive}, S \equiv F\,A \)
--
type Cotraversal1 s t a b = forall p. (Coaffine p, Cotraversing1 p) => Optic p s t a b

type Traversal0' s a = Traversal0 s s a a

type Cotraversal0' t b = Cotraversal0 t t b b

type Traversal' s a = Traversal s s a a

type Cotraversal' t b = Cotraversal1 t t b b

type Traversal1' s a = Traversal1 s s a a

type Cotraversal1' t b = Cotraversal1 t t b b

---------------------------------------------------------------------
-- Fold
---------------------------------------------------------------------

type Fold0 s a = forall p. (Affine p, CoercingR p) => Optic' p s a 

type Fold s a = forall p. (Affine p, Traversing p, CoercingR p) => Optic' p s a

type Fold1 s a = forall p. (Strong p, Traversing1 p, CoercingR p) => Optic' p s a 

type Cofold0 t b = forall p. (Coaffine p, CoercingL p) => Optic' p t b 

type Cofold t b = forall p. (Coaffine p, Cotraversing p, CoercingL p) => Optic' p t b

type Cofold1 t b = forall p. (Coaffine p, Cotraversing1 p, CoercingL p) => Optic' p t b 

---------------------------------------------------------------------
-- Rescan
---------------------------------------------------------------------

type Rescan s t a b = forall p. (Closed p, Rescanning p) => Optic p s t a b

type Rescan1 s t a b = forall p. (Coaffine p, Rescanning1 p) => Optic p s t a b

type Rescan' t b = Rescan t t b b

type Rescan1' t b = Rescan1 t t b b

---------------------------------------------------------------------
-- Setter
---------------------------------------------------------------------

-- | \( \mathsf{Functor}\;S\;A = \exists F : \mathsf{Functor}, S \equiv F\,A \)
--
type Setter s t a b = forall p. (Affine p, Coaffine p, Mapping p) => Optic p s t a b

type Setter1 s t a b = forall p. (Strong p, Coaffine p, Mapping1 p) => Optic p s t a b

-- | \( \quad \mathsf{Resetter}\;S\;A = \exists n : \mathbb{N}, S \cong \mathsf{Fin}\,n \to A \)
--
-- See also section 3 on Kaleidoscopes < https://cs.ttu.ee/events/nwpt2019/abstracts/paper14.pdf here >.
--
type Resetter s t a b = forall p. (Affine p, Closed p, Remapping p) => Optic p s t a b 

type Resetter1 s t a b = forall p. (Affine p, Coaffine p, Remapping1 p) => Optic p s t a b 

type Setter' s a = Setter s s a a

type Resetter' s a = Resetter s s a a

type Setter1' s a = Setter1 s s a a

type Resetter1' s a = Resetter1 s s a a

---------------------------------------------------------------------
-- View
---------------------------------------------------------------------

type View s a = forall p. (Strong p, CoercingR p) => Optic' p s a 

type Review t b = forall p. (Closed p, CoercingL p) => Optic' p t b

---------------------------------------------------------------------
-- 'Re' 
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

-- | Reverse an optic to obtain its dual.
--
-- @
-- 're' . 're'  ≡ id
-- @
--
-- @
-- 're' :: 'Iso' s t a b   -> 'Iso' b a t s
-- 're' :: 'Lens' s t a b  -> 'Colens' b a t s
-- 're' :: 'Prism' s t a b -> 'Coprism' b a t s
-- 're' :: 'Traversal' s t a b  -> 'Cotraversal' b a t s
-- 're' :: 'View' s t a b  -> 'Review' b a t s
-- @
--
-- >>> 5 ^. re left'
-- Left 5
--
re :: Optic (Re p a b) s t a b -> Optic p b a t s
re o = (between runRe Re) o id
{-# INLINE re #-}

-- | The 'Re' type and its instances witness the symmetry between the parameters of a 'Profunctor'.
--
newtype Re p s t a b = Re { runRe :: p b a -> p t s }

-- TODO: Closed, Representable, Corepresentable instances
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

instance (Profunctor p, forall x. Contravariant (p x)) => Bifunctor (Re p s t) where
  first f (Re p) = Re (p . contramap f)

  second f (Re p) = Re (p . lmap f)

instance Bifunctor p => Contravariant (Re p s t a) where
  contramap f (Re p) = Re (p . first f)

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
-- used for Choice operations on Cotraversals & Cofolds
instance Coapplicative f => Choice (Costar f) where
  left' (Costar f) = Costar $ either (Left . f) (Right . copure) . coapply
#endif

{-
unright' :: Coapplicative f => Star f (Either a b) (Either a c) -> Star f b c
unright' (Star f) = Star (go . Right) where go = either (go . Left) id . B.first copure . coapply . f
-}

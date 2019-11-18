{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE QuantifiedConstraints #-}
module Data.Profunctor.Optic.Type (
    -- * Optics
    Optic, Optic', between
    -- * Equality
  , Equality, Equality', As
    -- * Isos
  , Iso, Iso'
    -- * Lenses & Colenses
  , Lens, Lens', Lenslike, Lenslike'
  , Colens, Colens', Colenslike, Colenslike'
    -- * Prisms & Coprisms
  , Prism, Prism', Prismlike, Prismlike'
  , Coprism, Coprism', Coprismlike, Coprismlike'
    -- * Grates
  , Grate, Grate', Gratelike, Gratelike'
    -- * Repns & Corepns
  , Repn, Repn', Repnlike, Repnlike', ARepn, ARepn'
  , Corepn, Corepn', Corepnlike, Corepnlike', ACorepn, ACorepn'
    -- * Affine traversals, general & non-empty traversals, & cotraversals
  , Traversal0, Traversal0', Traversal0like, Traversal0like'
  , Traversal, Traversal', Traversallike, Traversallike', ATraversal, ATraversal'
  , Traversal1, Traversal1', Traversal1like, Traversal1like', ATraversal1, ATraversal1'
  , Cotraversal, Cotraversal', Cotraversallike, Cotraversallike', ACotraversal, ACotraversal'
    -- * Affine folds, general & non-empty folds, & unfolds
  , Fold0, Fold0like
  , Fold, Foldlike, FoldRep, AFold
  , Unfold, UnfoldRep, AUnfold
    -- * Non-empty folds
  , Fold1, Fold1like, AFold1
    -- * Views & Reviews
  , View, AView, PrimView, PrimViewlike, Review, AReview, PrimReview, PrimReviewlike
    -- * Setters & Resetters
  , Setter, Setter', Setterlike, ASetter, ASetter', Resetter, Resetter', Resetterlike, AResetter, AResetter'
    -- * 'Re'
  , Re(..), re
  , module Export
) where

import Data.Bifunctor (Bifunctor(..))
import Data.Functor.Apply (Apply(..))
import Data.Profunctor.Optic.Import
import Data.Profunctor.Types as Export
import Data.Profunctor.Strong as Export (Strong(..), Costrong(..))
import Data.Profunctor.Choice as Export (Choice(..), Cochoice(..))
import Data.Profunctor.Closed as Export (Closed(..))
import Data.Profunctor.Sieve as Export (Sieve(..), Cosieve(..))
import Data.Profunctor.Rep as Export (Representable(..), Corepresentable(..))

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :load Data.Profunctor.Optic

---------------------------------------------------------------------
-- 'Optic'
---------------------------------------------------------------------

type Optic p s t a b = p a b -> p s t

type Optic' p s a = Optic p s s a a

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
-- 'Equality'
---------------------------------------------------------------------

type Equality s t a b = forall p. Optic p s t a b

type Equality' s a = Equality s s a a

type As a = Equality' a a

---------------------------------------------------------------------
-- 'Iso'
---------------------------------------------------------------------

-- | 'Iso'
--
-- \( \mathsf{Iso}\;S\;A = S \cong A \)
--
-- For any valid 'Iso' /o/ we have:
-- @
-- o . re o ≡ id
-- re o . o ≡ id
-- view o (review o b) ≡ b
-- review o (view o s) ≡ s
-- @
--
type Iso s t a b = forall p. Profunctor p => Optic p s t a b

type Iso' s a = Iso s s a a

---------------------------------------------------------------------
-- 'Lens' & 'Colens'
---------------------------------------------------------------------

-- | Lenses access one piece of a product.
--
-- \( \mathsf{Lens}\;S\;A  = \exists C, S \cong C \times A \)
--
type Lens s t a b = forall p. Lenslike p s t a b

type Lens' s a = Lens s s a a

type Lenslike p s t a b = Strong p => Optic p s t a b

type Lenslike' p s a = Lenslike p s s a a

type Colens s t a b = forall p. Colenslike p s t a b

type Colens' s a = Colens s s a a

type Colenslike p s t a b = Costrong p => Optic p s t a b

type Colenslike' p s a = Colenslike p s s a a

---------------------------------------------------------------------
-- 'Prism' & 'Coprism'
---------------------------------------------------------------------

-- | Prisms access one piece of a sum.
--
-- \( \mathsf{Prism}\;S\;A = \exists D, S \cong D + A \)
--
type Prism s t a b = forall p. Prismlike p s t a b

type Prism' s a = Prism s s a a

type Prismlike p s t a b = Choice p => Optic p s t a b

type Prismlike' p s a = Prismlike p s s a a

type Coprism s t a b = forall p. Coprismlike p s t a b

type Coprism' s a = Coprism s s a a

type Coprismlike p s t a b = Cochoice p => Optic p s t a b

type Coprismlike' p s a = Coprismlike p s s a a

---------------------------------------------------------------------
-- 'Grate'
---------------------------------------------------------------------

-- | Grates access the codomain of a function.
--
--  \( \mathsf{Grate}\;S\;A = \exists I, S \cong I \to A \)
--
type Grate s t a b = forall p. Gratelike p s t a b

type Grate' s a = Grate s s a a

type Gratelike p s t a b = Closed p => Optic p s t a b

type Gratelike' p s a = Gratelike p s s a a

---------------------------------------------------------------------
-- 'Repn' & 'Corepn'
---------------------------------------------------------------------

type Repn s t a b = forall p. Repnlike p s t a b

type Repn' s a = Repn s s a a

type Repnlike p s t a b = Representable p => Optic p s t a b

type Repnlike' p s a = Repnlike p s s a a

type ARepn f s t a b = Optic (Star f) s t a b

type ARepn' f s a = ARepn f s s a a

type Corepn s t a b = forall p. Corepnlike p s t a b

type Corepn' s a = Corepn s s a a

type Corepnlike p s t a b = Corepresentable p => Optic p s t a b

type Corepnlike' p s a = Corepnlike p s s a a

type ACorepn f s t a b = Optic (Costar f) s t a b

type ACorepn' f s a = ACorepn f s s a a

---------------------------------------------------------------------
-- 'Traversal0', 'Traversal' , 'Traversal1', & 'Cotraversal'
---------------------------------------------------------------------

-- | A 'Traversal0' processes at most one part of the whole, with no interactions.
--
-- \( \mathsf{Traversal0}\;S\;A = \exists C, D, S \cong D + C \times A \)
--
type Traversal0 s t a b = forall p. Traversal0like p s t a b

type Traversal0' s a = Traversal0 s s a a

type Traversal0like p s t a b = Strong p => Choice p => Optic p s t a b

type Traversal0like' p s a = Traversal0like p s s a a

-- | A 'Traversal' processes 0 or more parts of the whole, with 'Applicative' interactions.
--
-- \( \mathsf{Traversal}\;S\;A = \exists F : \mathsf{Traversable}, S \equiv F\,A \)
--
type Traversal s t a b = forall p. Traversallike p s t a b

type Traversal' s a = Traversal s s a a

type Traversallike p s t a b = Choice p => Applicative (Rep p) => Repnlike p s t a b

type Traversallike' p s a = Traversallike p s s a a

type ATraversal f s t a b = Applicative f => ARepn f s t a b

type ATraversal' f s a = ATraversal f s s a a

-- | A 'Traversal1' processes 1 or more parts of the whole, with 'Apply' interactions.
--
-- \( \mathsf{Traversal1}\;S\;A = \exists F : \mathsf{Traversable1}, S \equiv F\,A \)
--
type Traversal1 s t a b = forall p. Traversal1like p s t a b

type Traversal1' s a = Traversal1 s s a a

type Traversal1like p s t a b = Choice p => Apply (Rep p) => Repnlike p s t a b

type Traversal1like' p s a = Traversal1like p s s a a

type ATraversal1 f s t a b = Apply f => ARepn f s t a b

type ATraversal1' f s a = ATraversal1 f s s a a

type Cotraversal s t a b = forall p. Cotraversallike p s t a b

type Cotraversal' s a = Cotraversal s s a a

type Cotraversallike p s t a b = Closed p => Choice p => ComonadApply (Corep p) => Corepnlike p s t a b

type Cotraversallike' p s a = Cotraversallike p s s a a

type ACotraversal f s t a b = ComonadApply f => ACorepn f s t a b

type ACotraversal' f s a = ACotraversal f s s a a

---------------------------------------------------------------------
-- 'Fold0', 'Fold', 'Fold1' & 'Unfold'
---------------------------------------------------------------------

-- | A 'Fold0' combines at most one element, with no interactions.
--
type Fold0 s a = forall p. Fold0like p s a

type Fold0like p s a = (forall x. Contravariant (p x)) => Traversal0like p s s a a

-- | A 'Fold' combines 0 or more elements, with 'Monoid' interactions.
--
type Fold s a = forall p. Foldlike p s a

type Foldlike p s a = (forall x. Contravariant (p x)) => Traversallike p s s a a

type FoldRep r = Star (Const r)

type AFold r s a = Monoid r => Optic' (FoldRep r) s a

-- | A 'Fold1' combines 1 or more elements, with 'Semigroup' interactions.
--
type Fold1 s a = forall p. Fold1like p s a

type Fold1like p s a = (forall x. Contravariant (p x)) => Traversal1like p s s a a

type AFold1 r s a = Semigroup r => Optic' (FoldRep r) s a

type Unfold t b = forall p. Unfoldlike p t b

type Unfoldlike p t b = Bifunctor p => Cotraversallike p t t b b

type UnfoldRep r = Costar (Const r)

type AUnfold r t b = Optic' (UnfoldRep r) t b

---------------------------------------------------------------------
-- 'View' & 'Review'
---------------------------------------------------------------------

-- | A 'View' extracts a result.
--
type View s a = forall p. Strong p => PrimViewlike p s s a a

type PrimView s t a b = forall p. PrimViewlike p s t a b

type PrimViewlike p s t a b = Profunctor p => (forall x. Contravariant (p x)) => Optic p s t a b

type AView s a = Optic' (FoldRep a) s a

-- | A 'Review' produces a result.
--
type Review t b = forall p. Costrong p => PrimReviewlike p t t b b

type PrimReview s t a b = forall p. PrimReviewlike p s t a b

type PrimReviewlike p s t a b = Profunctor p => Bifunctor p => Optic p s t a b

type AReview t b = Optic' Tagged t b

---------------------------------------------------------------------
-- 'Setter' & 'Resetter'
---------------------------------------------------------------------

-- | A 'Setter' modifies part of a structure.
--
-- \( \mathsf{Setter}\;S\;A = \exists F : \mathsf{Functor}, S \equiv F\,A \)
--
type Setter s t a b = forall p. Setterlike p s t a b

type Setter' s a = Setter s s a a

type Setterlike p s t a b = Closed p => Distributive (Rep p) => Traversallike p s t a b

type ASetter s t a b = ARepn Identity s t a b

type ASetter' s a = ASetter s s a a 

type Resetter s t a b = forall p. Resetterlike p s t a b

type Resetter' s a = Resetter s s a a

type Resetterlike p s t a b = Strong p => Traversable1 (Corep p) => Cotraversallike p s t a b

type AResetter s t a b = ACorepn Identity s t a b

type AResetter' s a = AResetter s s a a

---------------------------------------------------------------------
-- 'Re' 
---------------------------------------------------------------------

-- | Reverse an optic to obtain its dual.
--
-- >>> 5 ^. re left
-- Left 5
--
-- >>> 6 ^. re (left . from succ)
-- Left 7
--
-- @
-- 'review'  ≡ 'view'  '.' 're'
-- 'reviews' ≡ 'views' '.' 're'
-- 'reuse'   ≡ 'use'   '.' 're'
-- 'reuses'  ≡ 'uses'  '.' 're'
-- @
--
-- @
-- 're' :: 'Iso' s t a b   -> 'Iso' b a t s
-- 're' :: 'Lens' s t a b  -> 'Colens' b a t s
-- 're' :: 'Prism' s t a b -> 'Coprism' b a t s
-- @
--
re :: Optic (Re p a b) s t a b -> Optic p b a t s
re o = (between runRe Re) o id
{-# INLINE re #-}

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

instance (Profunctor p, forall x. Contravariant (p x)) => Bifunctor (Re p s t) where
  first f (Re p) = Re (p . contramap f)

  second f (Re p) = Re (p . lmap f)

---------------------------------------------------------------------
-- Orphan instances 
---------------------------------------------------------------------

instance Bifunctor p => Contravariant (Re p s t a) where
  contramap f (Re p) = Re (p . first f)

instance Contravariant f => Contravariant (Star f a) where
  contramap f (Star g) = Star $ contramap f . g

instance Contravariant f => Bifunctor (Costar f) where
  first f (Costar g) = Costar $ g . contramap f

  second f (Costar g) = Costar $ f . g

instance Cochoice (Forget r) where 
  unleft (Forget f) = Forget $ f . Left

  unright (Forget f) = Forget $ f . Right

instance Comonad f => Strong (Costar f) where
  first' (Costar f) = Costar $ \x -> (f (fmap fst x), snd (extract x))

  second' (Costar f) = Costar $ \x -> (fst (extract x), f (fmap snd x))

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
    -- * Lenses & Relenses
  , Lens, Lens', LensLike, LensLike'
  , Relens, Relens', RelensLike, RelensLike'
    -- * Prisms & Reprisms
  , Prism, Prism', PrismLike, PrismLike'
  , Reprism, Reprism', ReprismLike, ReprismLike'
    -- * Grates
  , Grate, Grate', GrateLike, GrateLike'
    -- * Repns & Corepns
  , Repn, Repn', RepnLike, RepnLike', ARepn
  , Corepn, Corepn', CorepnLike, CorepnLike', ACorepn
    -- * Affine traversals, general & non-empty traversals, & cotraversals
  , Traversal0, Traversal0', Traversal0Like, Traversal0Like'
  , Traversal, Traversal', TraversalLike, TraversalLike', ATraversal, ATraversal'
  , Traversal1, Traversal1', Traversal1Like, Traversal1Like', ATraversal1, ATraversal1'
  , Cotraversal, Cotraversal', CotraversalLike, CotraversalLike', ACotraversal, ACotraversal'
    -- * Affine folds, general & non-empty folds, & unfolds
  , Fold0, Fold0Like
  , Fold, FoldLike, FoldRep, AFold, Cayley, CayleyM
  , Unfold, UnfoldRep, AUnfold
    -- * Non-empty folds
  , Fold1, Fold1Like, AFold1
    -- * Views & Reviews
  , View, AView, PrimView, PrimViewLike, Review, AReview, PrimReview, PrimReviewLike
    -- * Setters & Resetters
  , Setter, Setter', SetterLike, ASetter, ASetter', Resetter, Resetter', ResetterLike, AResetter, AResetter'
    -- * 'Re'
  , Re(..), re
  , module Export
) where

import Control.Foldl (EndoM)
import Data.Bifunctor (Bifunctor(..))
import Data.Functor.Apply (Apply(..))
import Data.Monoid (Endo)
import Data.Profunctor.Optic.Import
import Data.Profunctor.Types as Export
import Data.Profunctor.Orphan as Export ()
import Data.Profunctor.Strong as Export (Strong(..), Costrong(..))
import Data.Profunctor.Choice as Export (Choice(..), Cochoice(..))
import Data.Profunctor.Closed as Export (Closed(..))
import Data.Profunctor.Sieve as Export (Sieve(..), Cosieve(..))
import Data.Profunctor.Rep as Export (Representable(..), Corepresentable(..))

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
-- 'Lens' & 'Relens'
---------------------------------------------------------------------

-- | Lenses access one piece of a product.
--
-- \( \mathsf{Lens}\;S\;A  = \exists C, S \cong C \times A \)
--
type Lens s t a b = forall p. LensLike p s t a b

type Lens' s a = Lens s s a a

type LensLike p s t a b = Strong p => Optic p s t a b

type LensLike' p s a = LensLike p s s a a

type Relens s t a b = forall p. RelensLike p s t a b

type Relens' s a = Relens s s a a

type RelensLike p s t a b = Costrong p => Optic p s t a b

type RelensLike' p s a = RelensLike p s s a a

---------------------------------------------------------------------
-- 'Prism' & 'Reprism'
---------------------------------------------------------------------

-- | Prisms access one piece of a sum.
--
-- \( \mathsf{Prism}\;S\;A = \exists D, S \cong D + A \)
--
type Prism s t a b = forall p. PrismLike p s t a b

type Prism' s a = Prism s s a a

type PrismLike p s t a b = Choice p => Optic p s t a b

type PrismLike' p s a = PrismLike p s s a a

type Reprism s t a b = forall p. ReprismLike p s t a b

type Reprism' s a = Reprism s s a a

type ReprismLike p s t a b = Cochoice p => Optic p s t a b

type ReprismLike' p s a = ReprismLike p s s a a

---------------------------------------------------------------------
-- 'Grate'
---------------------------------------------------------------------

-- | Grates access the codomain of a function.
--
--  \( \mathsf{Grate}\;S\;A = \exists I, S \cong I \to A \)
--
type Grate s t a b = forall p. GrateLike p s t a b

type Grate' s a = Grate s s a a

type GrateLike p s t a b = Closed p => Optic p s t a b

type GrateLike' p s a = GrateLike p s s a a

---------------------------------------------------------------------
-- 'Repn' & 'Corepn'
---------------------------------------------------------------------

type Repn s t a b = forall p. RepnLike p s t a b

type Repn' s a = Repn s s a a

type RepnLike p s t a b = Representable p => Optic p s t a b

type RepnLike' p s a = RepnLike p s s a a

type ARepn f s t a b = Optic (Star f) s t a b

type Corepn s t a b = forall p. CorepnLike p s t a b

type Corepn' s a = Corepn s s a a

type CorepnLike p s t a b = Corepresentable p => Optic p s t a b

type CorepnLike' p s a = CorepnLike p s s a a

type ACorepn f s t a b = Optic (Costar f) s t a b

---------------------------------------------------------------------
-- 'Traversal0', 'Traversal' , 'Traversal1', & 'Cotraversal'
---------------------------------------------------------------------

-- | A 'Traversal0' processes at most one part of the whole, with no interactions.
--
-- \( \mathsf{Traversal0}\;S\;A = \exists C, D, S \cong D + C \times A \)
--
type Traversal0 s t a b = forall p. Traversal0Like p s t a b

type Traversal0' s a = Traversal0 s s a a

type Traversal0Like p s t a b = Strong p => Choice p => Optic p s t a b

type Traversal0Like' p s a = Traversal0Like p s s a a

-- | A 'Traversal' processes 0 or more parts of the whole, with 'Applicative' interactions.
--
-- \( \mathsf{Traversal}\;S\;A = \exists F : \mathsf{Traversable}, S \equiv F\,A \)
--
type Traversal s t a b = forall p. TraversalLike p s t a b

type Traversal' s a = Traversal s s a a

type TraversalLike p s t a b = Choice p => Applicative (Rep p) => RepnLike p s t a b

type TraversalLike' p s a = TraversalLike p s s a a

type ATraversal f s t a b = Applicative f => Optic (Star f) s t a b

type ATraversal' f s a = ATraversal f s s a a

-- | A 'Traversal1' processes 1 or more parts of the whole, with 'Apply' interactions.
--
-- \( \mathsf{Traversal1}\;S\;A = \exists F : \mathsf{Traversable1}, S \equiv F\,A \)
--
type Traversal1 s t a b = forall p. Traversal1Like p s t a b

type Traversal1' s a = Traversal1 s s a a

type Traversal1Like p s t a b = Choice p => Apply (Rep p) => RepnLike p s t a b

type Traversal1Like' p s a = Traversal1Like p s s a a

type ATraversal1 f s t a b = Apply f => Optic (Star f) s t a b

type ATraversal1' f s a = ATraversal1 f s s a a

type Cotraversal s t a b = forall p. CotraversalLike p s t a b

type Cotraversal' s a = Cotraversal s s a a

type CotraversalLike p s t a b = Closed p => Choice p => CorepnLike p s t a b

type CotraversalLike' p s a = CotraversalLike p s s a a

type Cotraversal1Like p s t a b = Closed p => Choice p => Comonad (Corep p) => CorepnLike p s t a b

type ACotraversal f s t a b = Functor f => Optic (Costar f) s t a b

type ACotraversal' f s a = ACotraversal f s s a a

---------------------------------------------------------------------
-- 'Fold0', 'Fold' & 'Unfold'
---------------------------------------------------------------------

-- | A 'Fold0' combines at most one element, with no interactions.
--
type Fold0 s a = forall p. Fold0Like p s a

type Fold0Like p s a = (forall x. Contravariant (p x)) => Traversal0Like p s s a a

-- | A 'Fold' combines 0 or more elements, with 'Monoid' interactions.
--
type Fold s a = forall p. FoldLike p s a

type FoldLike p s a = (forall x. Contravariant (p x)) => TraversalLike p s s a a

type FoldRep r = Star (Const r)

type AFold r s a = Monoid r => Optic' (FoldRep r) s a

-- | Any lens, traversal, or prism will type-check as a `Cayley`
--
type Cayley s a = forall r. AFold (Endo (Endo r)) s a

type CayleyM m s a = forall r. AFold (Endo (EndoM m r)) s a 

type Unfold t b = forall p. UnfoldLike p t b

type UnfoldLike p t b = Bifunctor p => CotraversalLike p t t b b

type UnfoldRep r = Costar (Const r)

type AUnfold r t b = Optic' (UnfoldRep r) t b

---------------------------------------------------------------------
-- 'Fold1'
---------------------------------------------------------------------

-- | A 'Fold1' combines 1 or more elements, with 'Semigroup' interactions.
--
type Fold1 s a = forall p. Fold1Like p s a

type Fold1Like p s a = (forall x. Contravariant (p x)) => Traversal1Like p s s a a

type AFold1 r s a = Semigroup r => Optic' (FoldRep r) s a

---------------------------------------------------------------------
-- 'View' & 'Review'
---------------------------------------------------------------------

-- | A 'View' extracts a result.
--
type View s a = forall p. Strong p => PrimViewLike p s s a a

type PrimView s t a b = forall p. PrimViewLike p s t a b

type PrimViewLike p s t a b = Profunctor p => (forall x. Contravariant (p x)) => Optic p s t a b

type AView s a = Optic' (FoldRep a) s a

-- | A 'Review' produces a result.
--
type Review t b = forall p. Costrong p => PrimReviewLike p t t b b

type PrimReview s t a b = forall p. PrimReviewLike p s t a b

type PrimReviewLike p s t a b = Profunctor p => Bifunctor p => Optic p s t a b

type AReview t b = Optic' Tagged t b

---------------------------------------------------------------------
-- 'Setter' & 'Resetter'
---------------------------------------------------------------------

-- | A 'Setter' modifies part of a structure.
--
-- \( \mathsf{Setter}\;S\;A = \exists F : \mathsf{Functor}, S \equiv F\,A \)
--
type Setter s t a b = forall p. SetterLike p s t a b

type Setter' s a = Setter s s a a

type SetterLike p s t a b = Closed p => Distributive (Rep p) => TraversalLike p s t a b

type ASetter s t a b = ARepn Identity s t a b

type ASetter' s a = ASetter s s a a 

type Resetter s t a b = forall p. ResetterLike p s t a b

type Resetter' s a = Resetter s s a a

type ResetterLike p s t a b = Strong p => Traversable1 (Corep p) => CotraversalLike p s t a b

type AResetter s t a b = ACorepn Identity s t a b

type AResetter' s a = AResetter s s a a

---------------------------------------------------------------------
-- 'Re' 
---------------------------------------------------------------------

-- | Turn a 'Lens', 'Prism' or 'Iso' around to build its dual.
--
-- If you have an 'Iso', 'from' is a more powerful version of this function
-- that will return an 'Iso' instead of a mere 'View'.
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
-- 're' :: 'Prism' s t a b -> 'Reprism' b t
-- 're' :: 'Iso' s t a b   -> 'View' b t
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

instance Bifunctor p => Contravariant (Re p s t a) where
  contramap f (Re p) = Re (p . first f)

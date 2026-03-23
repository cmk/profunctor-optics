{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.Profunctor.Optic.Types (
    Optic, Optic'
    -- * Optics
    -- ** Ixoptic
  , Ix, Ix'
  , Ixoptic, Ixoptic'
    -- * Equality
    -- $equality
  , Equality, Equality'
    -- * Iso
    -- $iso
  , Iso, Iso'
    -- ** Lens, Ixlens
    -- $lens
  , Lens, Lens'
  , Ixlens, Ixlens'
    -- ** Prism, Ixprism
    -- $prism
  , Prism, Prism'
  , Ixprism, Ixprism'
    -- ** Traversal, Ixtraversal
    -- $traversal
  , Traversal, Traversal'
  , Ixtraversal, Ixtraversal'
    -- ** Traversal0, Ixtraversal0
    -- $traversal0
  , Traversal0, Traversal0'
  , Ixtraversal0, Ixtraversal0'
    -- ** Traversal1, Ixtraversal1
    -- $traversal1
  , Traversal1, Traversal1'
  , Ixtraversal1, Ixtraversal1'
    -- ** Fold, Ixfold
    -- $fold
  , Fold, Ixfold
    -- ** Fold0, Ixfold0
    -- $fold0
  , Fold0, Ixfold0
    -- ** Fold1, Ixfold1
    -- $fold1
  , Fold1, Ixfold1
    -- ** View, Ixview
    -- $view
  , View, Ixview
    -- ** Setter, Ixsetter
    -- $setter
  , Setter, Setter'
  , Ixsetter, Ixsetter'
    -- ** Setter1, Ixsetter1
    -- $setter1
  , Setter1, Setter1'
  , Ixsetter1, Ixsetter1'
    -- * Dual Optics
    -- ** Cxoptic
  , Cx, Cx'
  , Cxoptic, Cxoptic'
    -- ** Colens, Cxlens
    -- $colens
  , Colens, Colens'
  , Cxlens, Cxlens'
    -- ** Relens, Rxlens
    -- $relens
  , Relens, Relens'
  , Rxlens, Rxlens'
    -- ** Reprism, Rxprism
    -- $reprism
  , Reprism, Reprism'
  , Rxprism, Rxprism'
    -- ** Cotraversal, Cxtraversal
    -- $cotraversal
  , Cotraversal, Cotraversal'
  , Cxtraversal, Cxtraversal'
    -- ** Cotraversal0, Cxtraversal0
    -- $cotraversal0
  , Cotraversal0, Cotraversal0'
  , Cxtraversal0, Cxtraversal0'
    -- ** Cotraversal1, Cxtraversal1
    -- $cotraversal1
  , Cotraversal1, Cotraversal1'
  , Cxtraversal1, Cxtraversal1'
    -- ** Cofold, Cxfold
    -- $cofold
  , Cofold, Cxfold
    -- ** Cofold0, Cxfold0
    -- $cofold0
  , Cofold0, Cxfold0
    -- ** Cofold1, Cxfold1
    -- $cofold1
  , Cofold1, Cxfold1
    -- ** Review, Rxview
    -- $review
  , Review, Rxview
    -- ** Cosetter, Cxsetter
    -- $cosetter
  , Cosetter, Cosetter'
  , Cxsetter, Cxsetter'
    -- ** Cosetter1, Cxsetter1
    -- $cosetter1
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
import Data.Profunctor.Optic.Import
import Data.Profunctor.Types as Export

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :load Data.Profunctor.Optic

---------------------------------------------------------------------
-- Optic
---------------------------------------------------------------------

type Optic p s t a b = p a b -> p s t

type Optic' p s a = Optic p s s a a

type Ix p k a b = p (k , a) b

type Ix' p a b = Ix p a b b

type Ixoptic p k s t a b = Ix p k a b -> Ix p k s t

type Ixoptic' p k s a = Ixoptic p k s s a a

---------------------------------------------------------------------
-- Equality
---------------------------------------------------------------------

-- $equality
-- \( \mathsf{Equality}\;A = A \cong A \)

type Equality s t a b = forall p. Optic p s t a b

type Equality' s a = Equality s s a a

---------------------------------------------------------------------
-- Iso
---------------------------------------------------------------------

-- $iso
-- \( \mathsf{Iso}\;S\;A = S \cong A \)

type Iso s t a b = forall p. Profunctor p => Optic p s t a b

type Iso' s a = Iso s s a a

---------------------------------------------------------------------
-- Lens
---------------------------------------------------------------------

-- $lens
-- \( \mathsf{Lens}\;S\;A  = \exists C, S \cong C \times A \)
--
-- \( \mathsf{Ixlens}\;K\;S\;A = \exists C, S \cong C \times (K \times A) \)

type Lens s t a b = forall p. Strong p => Optic p s t a b

type Lens' s a = Lens s s a a

type Ixlens k s t a b = forall p. Strong p => Ixoptic p k s t a b

type Ixlens' k s a = Ixlens k s s a a

---------------------------------------------------------------------
-- Prism
---------------------------------------------------------------------

-- $prism
-- \( \mathsf{Prism}\;S\;A = \exists C, S \cong C + A \)
--
-- \( \mathsf{Ixprism}\;K\;S\;A = \exists C, S \cong C + (K \times A) \)

type Prism s t a b = forall p. Choice p => Optic p s t a b

type Prism' s a = Prism s s a a

type Ixprism k s t a b = forall p. Choice p => Ixoptic p k s t a b

type Ixprism' k s a = Ixprism k s s a a

---------------------------------------------------------------------
-- Traversal
---------------------------------------------------------------------

-- $traversal
-- \( \mathsf{Traversal}\;S\;A = \exists F : \mathsf{Traversable}, S \equiv F\,A \)
--
-- \( \mathsf{Ixtraversal}\;K\;S\;A = \exists F : \mathsf{Traversable}, S \equiv F\,(K \times A) \)

type Traversal s t a b = forall p. (Affine p, Traversing p) => Optic p s t a b

type Traversal' s a = Traversal s s a a

type Ixtraversal k s t a b = forall p. (Affine p, Traversing p) => Ixoptic p k s t a b

type Ixtraversal' k s a = Ixtraversal k s s a a

-- $traversal0
-- \( \mathsf{Traversal0}\;S\;A = \exists C, D, S \cong D + C \times A \)
--
-- \( \mathsf{Ixtraversal0}\;K\;S\;A = \exists C, D, S \cong D + C \times (K \times A) \)

type Traversal0 s t a b = forall p. Affine p => Optic p s t a b

type Traversal0' s a = Traversal0 s s a a

type Ixtraversal0 k s t a b = forall p. Affine p => Ixoptic p k s t a b

type Ixtraversal0' k s a = Ixtraversal0 k s s a a

-- $traversal1
-- \( \mathsf{Traversal1}\;S\;A = \exists F : \mathsf{Traversable1}, S \equiv F\,A \)
--
-- \( \mathsf{Ixtraversal1}\;K\;S\;A = \exists F : \mathsf{Traversable1}, S \equiv F\,(K \times A) \)

type Traversal1 s t a b = forall p. (Strong p, Traversing1 p) => Optic p s t a b

type Traversal1' s a = Traversal1 s s a a

type Ixtraversal1 k s t a b = forall p. (Strong p, Traversing1 p) => Ixoptic p k s t a b

type Ixtraversal1' k s a = Ixtraversal1 k s s a a

---------------------------------------------------------------------
-- Fold
---------------------------------------------------------------------

-- $fold
-- \( \mathsf{Fold}\;S\;A = \exists F : \mathsf{Foldable}, S \equiv F\,A \)
--
-- \( \mathsf{Ixfold}\;K\;S\;A = \exists F : \mathsf{Foldable}, S \equiv F\,(K \times A) \)

type Fold s a = forall p. (Affine p, Traversing p, CoercingR p) => Optic' p s a

type Ixfold k s a = forall p. (Affine p, Traversing p, CoercingR p) => Ixoptic' p k s a

-- $fold0
-- \( \mathsf{Fold0}\;S\;A = \exists C, D, S \cong D + C \times A \)
--
-- \( \mathsf{Ixfold0}\;K\;S\;A = \exists C, D, S \cong D + C \times (K \times A) \)

type Fold0 s a = forall p. (Affine p, CoercingR p) => Optic' p s a

type Ixfold0 k s a = forall p. (Affine p, CoercingR p) => Ixoptic' p k s a

-- $fold1
-- \( \mathsf{Fold1}\;S\;A = \exists F : \mathsf{Foldable1}, S \equiv F\,A \)
--
-- \( \mathsf{Ixfold1}\;K\;S\;A = \exists F : \mathsf{Foldable1}, S \equiv F\,(K \times A) \)

type Fold1 s a = forall p. (Strong p, Traversing1 p, CoercingR p) => Optic' p s a

type Ixfold1 k s a = forall p. (Strong p, Traversing1 p, CoercingR p) => Ixoptic' p k s a

---------------------------------------------------------------------
-- View
---------------------------------------------------------------------

-- $view
-- \( \mathsf{View}\;S\;A = S \to A \)
--
-- \( \mathsf{Ixview}\;K\;S\;A = S \to K \times A \)

type View s a = forall p. (Strong p, CoercingR p) => Optic' p s a

type Ixview k s a = forall p. (Strong p, CoercingR p) => Ixoptic' p k s a

---------------------------------------------------------------------
-- Setter
---------------------------------------------------------------------

-- $setter
-- \( \mathsf{Setter}\;S\;A = \exists F : \mathsf{Functor}, S \equiv F\,A \)
--
-- \( \mathsf{Ixsetter}\;K\;S\;A = \exists F : \mathsf{Functor}, S \equiv F\,(K \times A) \)

type Setter s t a b = forall p. (Affine p, Traversing p, Mapping p) => Optic p s t a b

type Setter' s a = Setter s s a a

type Ixsetter k s t a b = forall p. (Affine p, Traversing p, Mapping p) => Ixoptic p k s t a b

type Ixsetter' k s a = Ixsetter k s s a a

-- $setter1
-- \( \mathsf{Setter1}\;S\;A = \exists F : \mathsf{Functor}, S \equiv F\,A \)
--
-- \( \mathsf{Ixsetter1}\;K\;S\;A = \exists F : \mathsf{Functor}, S \equiv F\,(K \times A) \)

type Setter1 s t a b = forall p. (Strong p, Traversing1 p, Mapping1 p) => Optic p s t a b

type Setter1' s a = Setter1 s s a a

type Ixsetter1 k s t a b = forall p. (Strong p, Traversing1 p, Mapping1 p) => Ixoptic p k s t a b

type Ixsetter1' k s a = Ixsetter1 k s s a a

---------------------------------------------------------------------
-- Dual Optics
---------------------------------------------------------------------

type Cx p k a b = p a (k -> b)

type Cx' p a b = Cx p a a b

type Cxoptic p k s t a b = Cx p k a b -> Cx p k s t

type Cxoptic' p k t b = Cxoptic p k t t b b

-- $colens
-- \( \mathsf{Colens}\;S\;A = \exists I, S \cong I \to A \)
--
-- \( \mathsf{Cxlens}\;K\;T\;B = \exists I, T \cong I \to (K \to B) \)

type Colens s t a b = forall p. Closed p => Optic p s t a b

type Colens' s a = Colens s s a a

type Cxlens k s t a b = forall p. Closed p => Cxoptic p k s t a b

type Cxlens' k t b = Cxlens k t t b b

-- $relens
-- \( \mathsf{Relens}\;S\;A = \exists C, A \cong C \times S \) (Re-reversed)
--
-- \( \mathsf{Rxlens}\;K\;S\;A = \exists C, A \cong C \times (K \times S) \) (Re-reversed)
--
-- The 'Re'-dual of 'Lens'. A 'Relens' is simultaneously a 'View' and a 'Review'.
--
-- @
-- 're' :: 'Lens' s t a b -> 'Relens' b a t s
-- @

type Relens s t a b = forall p. Costrong p => Optic p s t a b

type Relens' s a = Relens s s a a

type Rxlens k s t a b = forall p. Costrong p => Ixoptic p k s t a b

type Rxlens' k s a = Rxlens k s s a a

-- $reprism
-- \( \mathsf{Reprism}\;S\;A = \exists C, A \cong C + S \) (Re-reversed)
--
-- \( \mathsf{Rxprism}\;K\;S\;A = \exists C, A \cong C + (K \times S) \) (Re-reversed)
--
-- The 'Re'-dual of 'Prism'. A 'Reprism' is simultaneously a 'View' and a 'Review'.
--
-- @
-- 're' :: 'Prism' s t a b -> 'Reprism' b a t s
-- @

type Reprism s t a b = forall p. Cochoice p => Optic p s t a b

type Reprism' s a = Reprism s s a a

type Rxprism k s t a b = forall p. Cochoice p => Ixoptic p k s t a b

type Rxprism' k s a = Rxprism k s s a a

-- $cotraversal
-- \( \mathsf{Cotraversal}\;S\;A = \exists F : \mathsf{Distributive}, S \equiv F\,A \)
--
-- \( \mathsf{Cxtraversal}\;K\;T\;B = \exists G : \mathsf{Distributive}, T \equiv G\,(K \to B) \)

type Cotraversal s t a b = forall p. (Coaffine p, Cotraversing p) => Optic p s t a b

type Cotraversal' t b = Cotraversal t t b b

type Cxtraversal k s t a b = forall p. (Coaffine p, Cotraversing p) => Cxoptic p k s t a b

type Cxtraversal' k t b = Cxtraversal k t t b b

-- $cotraversal0
-- \( \mathsf{Cotraversal0}\;S\;A = \exists D, I, S \cong I \to D + A \)
--
-- \( \mathsf{Cxtraversal0}\;K\;T\;B = \exists D, I, T \cong I \to D + (K \to B) \)

type Cotraversal0 s t a b = forall p. Coaffine p => Optic p s t a b

type Cotraversal0' t b = Cotraversal0 t t b b

type Cxtraversal0 k s t a b = forall p. Coaffine p => Cxoptic p k s t a b

type Cxtraversal0' k t b = Cxtraversal0 k t t b b

-- $cotraversal1
-- \( \mathsf{Cotraversal1}\;S\;A = \exists F : \mathsf{Distributive1}, S \equiv F\,A \)
--
-- \( \mathsf{Cxtraversal1}\;K\;T\;B = \exists G : \mathsf{Distributive1}, T \equiv G\,(K \to B) \)

type Cotraversal1 s t a b = forall p. (Closed p, Cotraversing1 p) => Optic p s t a b

type Cotraversal1' t b = Cotraversal1 t t b b

type Cxtraversal1 k s t a b = forall p. (Closed p, Cotraversing1 p) => Cxoptic p k s t a b

type Cxtraversal1' k t b = Cxtraversal1 k t t b b

-- $cofold
-- \( \mathsf{Cofold}\;T\;B = \exists G : \mathsf{Distributive}, T \equiv G\,B \)
--
-- \( \mathsf{Cxfold}\;K\;T\;B = \exists G : \mathsf{Distributive}, T \equiv G\,(K \to B) \)

type Cofold t b = forall p. (Coaffine p, Cotraversing p, CoercingL p) => Optic' p t b

type Cxfold k t b = forall p. (Coaffine p, Cotraversing p, CoercingL p) => Cxoptic' p k t b

-- $cofold0
-- \( \mathsf{Cofold0}\;T\;B = \exists D, I, T \cong I \to D + B \)
--
-- \( \mathsf{Cxfold0}\;K\;T\;B = \exists D, I, T \cong I \to D + (K \to B) \)

type Cofold0 t b = forall p. (Coaffine p, CoercingL p) => Optic' p t b

type Cxfold0 k t b = forall p. (Coaffine p, CoercingL p) => Cxoptic' p k t b

-- $cofold1
-- \( \mathsf{Cofold1}\;T\;B = \exists G : \mathsf{Distributive1}, T \equiv G\,B \)
--
-- \( \mathsf{Cxfold1}\;K\;T\;B = \exists G : \mathsf{Distributive1}, T \equiv G\,(K \to B) \)

type Cofold1 t b = forall p. (Closed p, Cotraversing1 p, CoercingL p) => Optic' p t b

type Cxfold1 k t b = forall p. (Closed p, Cotraversing1 p, CoercingL p) => Cxoptic' p k t b

-- $review
-- \( \mathsf{Review}\;T\;B = B \to T \)
--
-- \( \mathsf{Rxview}\;K\;T\;B = (K \to B) \to T \)
--
-- /Note/: 'Review' currently uses @('Closed' p, 'CoercingL' p)@. By the
-- library's naming conventions this should be called @Coview@ (co-dual of
-- 'View', like 'Colens' is co-dual of 'Lens'). The true @Review@
-- (Re-dual, @'Costrong' p, 'CoercingL' p@) will be added in a future
-- release. See S17.28 in the sprint plan.

type Review t b = forall p. (Closed p, CoercingL p) => Optic' p t b

type Rxview k t b = forall p. (Closed p, CoercingL p) => Cxoptic' p k t b

-- $cosetter
-- \( \quad \mathsf{Cosetter}\;S\;A = \exists n : \mathbb{N}, S \cong \mathsf{Fin}\,n \to A \)
--
-- \( \quad \mathsf{Cxsetter}\;K\;T\;B = \exists n : \mathbb{N}, T \cong \mathsf{Fin}\,n \to (K \to B) \)
--
-- See also section 3 on Kaleidoscopes < https://cs.ttu.ee/events/nwpt2019/abstracts/paper14.pdf here >.

type Cosetter s t a b = forall p. (Coaffine p, Cotraversing p, Remapping p) => Optic p s t a b

type Cosetter' s a = Cosetter s s a a

type Cxsetter k s t a b = forall p. (Coaffine p, Cotraversing p, Remapping p) => Cxoptic p k s t a b

type Cxsetter' k t b = Cxsetter k t t b b

-- $cosetter1
-- \( \quad \mathsf{Cosetter1}\;S\;A = \exists n \geq 1, S \cong \mathsf{Fin}\,n \to A \)
--
-- \( \quad \mathsf{Cxsetter1}\;K\;T\;B = \exists n \geq 1, T \cong \mathsf{Fin}\,n \to (K \to B) \)

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
-- 'Re' can reverse optics built from classes that have a mirror image:
--
--   * 'Strong' \(\leftrightarrow\) 'Costrong'
--   * 'Choice' \(\leftrightarrow\) 'Cochoice'
--   * 'Bifunctor' \(\leftrightarrow\) 'Contravariant'
--
-- 'Re' cannot reverse 'Closed', 'Representable', or 'Corepresentable' because
-- these classes have no standard dual. A hypothetical @Coclosed@ with
-- @unclosed :: p (x -> a) (x -> b) -> p a b@ would enable @Closed p => Coclosed (Re p)@,
-- but no such class exists in the profunctor hierarchy. Consequently, 'Colens',
-- 'Cotraversal', and other 'Closed'-based optics cannot be reversed with 're'.
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

instance Contravariant f => Bifunctor (Costar f) where
  first f (Costar g) = Costar $ g . contramap f

  second f (Costar g) = Costar $ f . g

-- | Used for Choice operations (e.g. preview) on Cotraversals & Cofolds.
instance Coapplicative f => Choice (Costar f) where
  left' (Costar f) = Costar $ either (Left . f) (Right . copure) . coapply

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | The profunctor optic type hierarchy, structured as an adjunction
-- diamond.
--
-- Left (Star-side) carriers are characterized by 'Rep' p (a covariant
-- functor). Right (Costar-side) carriers are characterized by 'Corep' p
-- (used contravariantly). When @'Corep' p ⊣ 'Rep' p@ — i.e., the
-- representation functors form an adjunction — the profunctor is
-- 'Adjoining' and sits at the meet of the diamond.
--
-- @
--           Iso                       (Identity ⊣ Identity)
--          / | \\
--     Lens Prism Colens               (left and right adjoints)
--      |    |     |
--    Setter ... Cosetter              (full representation)
--       \\       /
--        Adjoint                      (Corep p ⊣ Rep p)
-- @
--
-- Left-indexed ('Ix') optics thread an index through the left adjoint
-- functor @(,) k@, while right-indexed ('Cx') optics thread a coindex
-- through the right adjoint functor @(->) k@.
module Data.Profunctor.Optic.Types (
    Optic, Optic'
  , Ix, Ix', Ixoptic, Ixoptic'
  , Cx, Cx', Cxoptic, Cxoptic'
    -- * Iso
    -- $equality
  , Equality, Equality'
    -- $iso
  , Iso, Iso'
    -- * Left Adjoint Optics (Star side)
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
    -- * Right Adjoint Optics (Costar side)
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
    -- ** Coview, Cxview
    -- $coview
  , Coview, Cxview
    -- ** Review
  , Review
    -- ** Cosetter, Cxsetter
    -- $cosetter
  , Cosetter, Cosetter'
  , Cxsetter, Cxsetter'
    -- ** Cosetter1, Cxsetter1
    -- $cosetter1
  , Cosetter1, Cosetter1'
  , Cxsetter1, Cxsetter1'
    -- * Adjoint Optics (both sides)
    -- $adjoint
  , Adjoint, Adjoint'
  , Ixadjoint, Ixadjoint'
  , Cxadjoint, Cxadjoint'
  , Adjoint1, Adjoint1'
  , Ixadjoint1, Ixadjoint1'
  , Cxadjoint1, Cxadjoint1'
    -- * Constraints
  , Affine, Coaffine
  , Traversing, Cotraversing
  , Traversing1, Cotraversing1
  , Mapping, Comapping
  , Mapping1, Comapping1
  , Adjoining, Adjoining1
  , CoercingL, CoercingR
  , Foldable', Foldable1'
  , module Export
) where


import Data.Bifunctor (Bifunctor(..))
import Data.Functor.Adjunction (Adjunction)
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
-- Adjoint
---------------------------------------------------------------------

-- $adjoint
-- An 'Adjoint' optic requires a profunctor that is simultaneously
-- 'Representable' ('Star'-like) and 'Corepresentable' ('Costar'-like),
-- with the representation functors forming an adjunction
-- @'Corep' p ⊣ 'Rep' p@.
--
-- The canonical 'Adjoining' profunctor is 'Conjoin' @j@, which sits
-- at the currying adjunction @(,) j ⊣ (->) j@. An 'Adjoint' optic
-- can freely convert between 'Star'-like and 'Costar'-like forms
-- via 'Data.Profunctor.Optic.Iso.adjuncted'.
--
-- \( \mathsf{Adjoint}\;S\;A = \exists F\,U, F \dashv U, S \cong F\,A \cong U^{-1}\,A \)

type Adjoint s t a b = forall p. Adjoining p => Optic p s t a b

type Adjoint' s a = Adjoint s s a a

type Ixadjoint k s t a b = forall p. Adjoining p => Ixoptic p k s t a b

type Ixadjoint' k s a = Ixadjoint k s s a a

type Adjoint1 s t a b = forall p. Adjoining1 p => Optic p s t a b

type Adjoint1' s a = Adjoint1 s s a a

type Ixadjoint1 k s t a b = forall p. Adjoining1 p => Ixoptic p k s t a b

type Ixadjoint1' k s a = Ixadjoint1 k s s a a

type Cxadjoint k s t a b = forall p. Adjoining p => Cxoptic p k s t a b

type Cxadjoint' k t b = Cxadjoint k t t b b

type Cxadjoint1 k s t a b = forall p. Adjoining1 p => Cxoptic p k s t a b

type Cxadjoint1' k t b = Cxadjoint1 k t t b b

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
-- The 'Re'-dual of 'Lens'. A 'Relens' is simultaneously a 'View' and a 'Coview'.
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
-- The 'Re'-dual of 'Prism'. A 'Reprism' is simultaneously a 'View' and a 'Coview'.
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

-- $coview
-- \( \mathsf{Coview}\;T\;B = B \to T \)
--
-- \( \mathsf{Cxview}\;K\;T\;B = (K \to B) \to T \)

-- | The Star\/Costar dual of 'View' (@Closed + CoercingL@).
--
-- Composes with the Closed chain: 'Colens', 'Cotraversal', 'Cofold'.
--
-- There is no @coview@ operator. Both 'Coview' and 'Review' monomorphize
-- to the same carrier ('Tagged'), so 'review' accepts either after
-- monomorphization. Passing a polymorphic @'Coview' t b@ directly to
-- 'review' will not typecheck — 'Closed' does not imply 'Costrong'.
--
-- For the relationship between the Star\/Costar and Strong\/Costrong
-- duality axes, see "Data.Profunctor.Optic.Dual".
--
type Coview t b = forall p. (Closed p, CoercingL p) => Optic' p t b

-- | Coindexed 'Coview'. The coindex @k@ threads via @k -> b@ on the
-- right of the profunctor ('Cxoptic''), producing an observable
-- @b -> (k -> t)@ through 'cxview'.
--
-- There is no @Rxview@ type or @rxview@ operator. The hypothetical
-- @Rxview@ would thread the coindex via @(k, b)@ on the left
-- ('Ixoptic''), but 'Tagged' discards the left component — so
-- @rxview@ would collapse to 'review'.
--
type Cxview k t b = forall p. (Closed p, CoercingL p) => Cxoptic' p k t b

---------------------------------------------------------------------
-- Review
---------------------------------------------------------------------

-- | \( \mathsf{Review}\;T\;B = B \to T \)
--
-- The Strong\/Costrong (Re-)dual of 'View'.
-- @'re' :: 'View' s a -> 'Review' a s@.
--
-- 'Review' (@'Costrong' + 'CoercingL'@) is distinct from 'Coview'
-- (@'Closed' + 'CoercingL'@) at the type level: 'Coview' composes with
-- the Closed chain (Colens, Cotraversal), while 'Review' composes with
-- the Costrong chain (Relens, Grate). At the carrier level both
-- monomorphize to 'Tagged', so 'review' accepts either.
--
-- See "Data.Profunctor.Optic.Dual" for how 're' relates 'View' to
-- 'Review', and why 'co' cannot relate 'View' to 'Coview' in the
-- same way.
--
type Review t b = forall p. (Costrong p, CoercingL p) => Optic' p t b

-- $cosetter
-- \( \quad \mathsf{Cosetter}\;S\;A = \exists n : \mathbb{N}, S \cong \mathsf{Fin}\,n \to A \)
--
-- \( \quad \mathsf{Cxsetter}\;K\;T\;B = \exists n : \mathbb{N}, T \cong \mathsf{Fin}\,n \to (K \to B) \)
--
-- See also section 3 on Kaleidoscopes < https://cs.ttu.ee/events/nwpt2019/abstracts/paper14.pdf here >.

type Cosetter s t a b = forall p. (Coaffine p, Cotraversing p, Comapping p) => Optic p s t a b

type Cosetter' s a = Cosetter s s a a

type Cxsetter k s t a b = forall p. (Coaffine p, Cotraversing p, Comapping p) => Cxoptic p k s t a b

type Cxsetter' k t b = Cxsetter k t t b b

-- $cosetter1
-- \( \quad \mathsf{Cosetter1}\;S\;A = \exists n \geq 1, S \cong \mathsf{Fin}\,n \to A \)
--
-- \( \quad \mathsf{Cxsetter1}\;K\;T\;B = \exists n \geq 1, T \cong \mathsf{Fin}\,n \to (K \to B) \)

type Cosetter1 s t a b = forall p. (Closed p, Cotraversing1 p, Comapping1 p) => Optic p s t a b

type Cosetter1' s a = Cosetter1 s s a a

type Cxsetter1 k s t a b = forall p. (Closed p, Cotraversing1 p, Comapping1 p) => Cxoptic p k s t a b

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

type Comapping p = (Closed p, Corepresentable p, Traversable (Corep p))

type Mapping1 p = (Representable p, Distributive1 (Rep p))

type Comapping1 p = (Closed p, Corepresentable p, Traversable1 (Corep p))

type Adjoining p = (Mapping p, Comapping p, Adjunction (Corep p) (Rep p))

type Adjoining1 p = (Mapping1 p, Comapping1 p, Adjunction (Corep p) (Rep p))

type CoercingL p = (Bifunctor p)

type CoercingR p = (forall x. Contravariant (p x))

type Foldable' f = (Functor f, Foldable f)

type Foldable1' f = (Functor f, Foldable1 f)

-- Re, Co, re, co, and between are defined in Data.Profunctor.Optic.Dual
-- and re-exported from this module.

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

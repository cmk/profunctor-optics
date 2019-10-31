{-# LANGUAGE UndecidableInstances, UndecidableSuperClasses, TypeOperators , GADTs, DataKinds, KindSignatures, TypeFamilies #-}

{-# LANGUAGE ExistentialQuantification #-}

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE QuantifiedConstraints #-}
-- {-# LANGUAGE IncoherentInstances #-}
-- {-# LANGUAGE RepnlappingInstances #-}


module Data.Profunctor.Optic.Type (
    -- * Optics
    Optic, Optic'
    -- * Equality
  , Equality, Equality', As
    -- * Isos
  , Iso, Iso'
    -- * Lenses & Relenses
  , Lens, Lens', LensLike, LensLike', Relens, Relens', RelensLike, RelensLike'
    -- * Prisms & Reprisms
  , Prism, Prism', PrismLike, PrismLike', Reprism, Reprism', ReprismLike, ReprismLike'
    -- * Grates
  , Grate, Grate', GrateLike, GrateLike'
    -- * Grids
  , Grid, Grid', GridLike, GridLike'
    -- * Repns
  , Repn, Repn', RepnLike, RepnLike', ARepn
    -- * Corepns
  , Corepn, Corepn', CorepnLike, CorepnLike', ACorepn
    -- * Affine traversals
  , Traversal0, Traversal0', Traversal0Like, Traversal0Like'
    -- * Non-empty traversals
  , Traversal1, Traversal1', Traversal1Like, Traversal1Like'
    -- * General traversals
  , Traversal, Traversal', TraversalLike, TraversalLike', ATraversal, ATraversal'
    -- * Affine cotraversals
  , Cotraversal0, Cotraversal0', Cotraversal0Like, Cotraversal0Like'
    -- * Cotraversals
  , Cotraversal, Cotraversal', CotraversalLike, CotraversalLike'
    -- * Affine folds
  , Fold0, Fold0Like
    -- * Non-empty folds
  , Fold1, Fold1Like, AFold1
    -- * General folds
  , Fold, FoldLike, FoldRep, AFold
    -- * Affine cofolds
  --, Cofold0, Cofold0Rep, ACofold0
    -- * Cofolds
  , Cofold, CofoldRep, ACofold
    -- * Views
  , View, AView, PrimView, PrimViewLike
    -- * Reviews
  , Review, AReview, PrimReview, PrimReviewLike
    -- * Setters
  , Setter, Setter', SetterLike, ASetter
    -- * Resetters
  , Resetter, Resetter', ResetterLike, AResetter
    -- * 'Re'
  , Re(..), re
  , module Export
) where

import Data.Semigroup (First, Last)
import Data.Profunctor.Optic.Prelude

import qualified Data.Profunctor.Optic.Type.VL as VL
import Control.Applicative
import Control.Monad
import Control.Comonad
import Control.Monad.Fix
import Data.Bifoldable
import Data.Bitraversable
import Data.Coerce
import Data.Data
import Data.Distributive
import Data.Functor.Classes
import Data.Functor.Apply (Apply(..))

import GHC.Generics (Generic)
import Data.Int
import Data.Word
import Data.Functor.Base (NonEmptyF(..))
import Data.Traversable

import Data.Bifunctor as Export (Bifunctor (..))


import qualified Data.Functor.Rep as F

---------------------------------------------------------------------
-- 'Optic'
---------------------------------------------------------------------

type Optic p s t a b = p a b -> p s t

type Optic' p s a = Optic p s s a a

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
type Iso s t a b = forall p. Profunctor p => Optic p s t a b

type Iso' s a = Iso s s a a

---------------------------------------------------------------------
-- 'Lens'
---------------------------------------------------------------------

-- | Lenses access one piece of a product structure.
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
-- 'Prism'
---------------------------------------------------------------------

-- | Prisms access one piece of a sum structure.
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

-- | Grates access the codomain of an indexed structure.
--
--  \( \mathsf{Grate}\;S\;A = \exists I, S \cong I \to A \)
--
type Grate s t a b = forall p. GrateLike p s t a b

type Grate' s a = Grate s s a a

type GrateLike p s t a b = Closed p => Optic p s t a b

type GrateLike' p s a = GrateLike p s s a a

---------------------------------------------------------------------
-- 'Grid'
---------------------------------------------------------------------

-- | Grids arise from the combination of lenses and grates.
--
--  \( \mathsf{Grid}\;S\;A = \exists C,I, S \cong C \times (I \to A) \)
--
type Grid s t a b = forall p. GridLike p s t a b

type Grid' s a = Grid s s a a

type GridLike p s t a b = Closed p => LensLike p s t a b

type GridLike' p s a = GridLike p s s a a

---------------------------------------------------------------------
-- 'Repn'
---------------------------------------------------------------------

type Repn s t a b = forall p. RepnLike p s t a b

type Repn' s a = Repn s s a a

type RepnLike p s t a b = Representable p => Optic p s t a b

type RepnLike' p s a = RepnLike p s s a a

type ARepn f s t a b = Optic (Star f) s t a b

---------------------------------------------------------------------
-- 'Corepn'
---------------------------------------------------------------------

type Corepn s t a b = forall p. CorepnLike p s t a b

type Corepn' s a = Corepn s s a a

type CorepnLike p s t a b = Corepresentable p => Optic p s t a b

type CorepnLike' p s a = CorepnLike p s s a a

type ACorepn f s t a b = Optic (Costar f) s t a b

---------------------------------------------------------------------
-- 'Birepn'
---------------------------------------------------------------------

type Birepn s t a b = forall p. BirepnLike p s t a b

type Birepn' s a = Birepn s s a a

type BirepnLike p s t a b = Representable p => Corepresentable p => Optic p s t a b

type BirepnLike' p s a = BirepnLike p s s a a

type ABirepn f g s t a b = Optic (Bistar f g) s t a b

---------------------------------------------------------------------
-- 'Traversal0'
---------------------------------------------------------------------

type Affine p = (Strong p, Choice p)

-- | A 'Traversal0' processes at most one element, with no interactions.
--
-- \( \mathsf{Traversal0}\;S\;A = \exists C, D, S \cong D + C \times A \)
--
type Traversal0 s t a b = forall p. Traversal0Like p s t a b

type Traversal0' s a = Traversal0 s s a a

type Traversal0Like p s t a b = Affine p => Optic p s t a b

type Traversal0Like' p s a = Traversal0Like p s s a a

---------------------------------------------------------------------
-- 'Traversal1'
---------------------------------------------------------------------

-- | A 'Traversal1' processes 1 or more elements, with non-empty applicative interactions.
--
type Traversal1 s t a b = forall p. Traversal1Like p s t a b

type Traversal1' s a = Traversal1 s s a a

type Traversal1Like p s t a b = Choice p => Apply (Rep p) => RepnLike p s t a b

type Traversal1Like' p s a = Traversal1Like p s s a a

---------------------------------------------------------------------
-- 'Traversal'
---------------------------------------------------------------------

-- | A 'Traversal' processes 0 or more elements, with applicative interactions.
--
type Traversal s t a b = forall p. TraversalLike p s t a b

type Traversal' s a = Traversal s s a a

type TraversalLike p s t a b = Affine p => Applicative (Rep p) => RepnLike p s t a b

type TraversalLike' p s a = TraversalLike p s s a a

type ATraversal f s t a b = Applicative f => Optic (Star f) s t a b

type ATraversal' f s a = ATraversal f s s a a

---------------------------------------------------------------------
-- 'Cotraversal0'
---------------------------------------------------------------------

type Coaffine p = (Closed p, Choice p)

-- | A 'Cotraversal0' arises from the combination of prisms and grates.
--
-- \( \mathsf{Cotraversal0}\;S\;A = \exists D,I, S \cong D + (I \to A) \)
--
type Cotraversal0 s t a b = forall p. Cotraversal0Like p s t a b

type Cotraversal0' s a = Cotraversal0 s s a a

type Cotraversal0Like p s t a b = Coaffine p => Optic p s t a b

type Cotraversal0Like' p s a = Cotraversal0Like p s s a a

---------------------------------------------------------------------
-- 'Cotraversal'
---------------------------------------------------------------------

type Cotraversal s t a b = forall p. CotraversalLike p s t a b

type Cotraversal' s a = Cotraversal s s a a

type CotraversalLike p s t a b = Coaffine p => CorepnLike p s t a b

type CotraversalLike' p s a = CotraversalLike p s s a a

---------------------------------------------------------------------
-- 'Cotraversal1'
---------------------------------------------------------------------

type Cotraversal1 s t a b = forall p. Cotraversal1Like p s t a b

type Cotraversal1' s a = Cotraversal1 s s a a

type Cotraversal1Like p s t a b = Coaffine p => Comonad (Corep p) => CorepnLike p s t a b

type Cotraversal1Like' p s a = Cotraversal1Like p s s a a

---------------------------------------------------------------------
-- 'Fold0'
---------------------------------------------------------------------

-- | A 'Fold0' extracts at most one non-summary result from a container.
--
type Fold0 s a = forall p. Fold0Like p s a

type Fold0Like p s a = (forall x. Contravariant (p x)) => Traversal0Like p s s a a

---------------------------------------------------------------------
-- 'Fold1'
---------------------------------------------------------------------

-- | A 'Fold1' extracts a semigroupal summary from a non-empty container
--
type Fold1 s a = forall p. Fold1Like p s a

type Fold1Like p s a = (forall x. Contravariant (p x)) => Traversal1Like p s s a a

type AFold1 r s a = Semigroup r => Optic' (FoldRep r) s a

---------------------------------------------------------------------
-- 'Fold'
---------------------------------------------------------------------

-- | A 'Fold' extracts a monoidal summary from a container.
--
type Fold s a = forall p. FoldLike p s a

type FoldLike p s a = (forall x. Contravariant (p x)) => TraversalLike p s s a a

type FoldRep r = Star (Const r)

type AFold r s a = Monoid r => Optic' (FoldRep r) s a

---------------------------------------------------------------------
-- 'Cofold0'
---------------------------------------------------------------------

type Cofold0 s a = forall p. Cofold0Like p s a

type Cofold0Like p s a = Bifunctor p => Cotraversal0Like p s s a a

---------------------------------------------------------------------
-- 'Cofold'
---------------------------------------------------------------------

type Cofold t b = forall p. CofoldLike p t b

type CofoldLike p t b = Bifunctor p => CotraversalLike p t t b b

type CofoldRep r = Costar (Const r)

type ACofold r t b = Optic' (CofoldRep r) t b

---------------------------------------------------------------------
-- 'View'
---------------------------------------------------------------------

-- | A 'View' extracts exactly one result.
--
type View s a = forall p. Strong p => PrimViewLike p s s a a

type PrimView s t a b = forall p. PrimViewLike p s t a b

type PrimViewLike p s t a b = Profunctor p => (forall x. Contravariant (p x)) => Optic p s t a b

type AView s a = Optic' (FoldRep a) s a

---------------------------------------------------------------------
-- 'Review'
---------------------------------------------------------------------

-- | A 'Review' produces a result.
type Review t b = forall p. Choice p => PrimReviewLike p t t b b

type PrimReview s t a b = forall p. PrimReviewLike p s t a b

type PrimReviewLike p s t a b = Profunctor p => Bifunctor p => Optic p s t a b

type AReview t b = Optic' (CofoldRep b) t b

---------------------------------------------------------------------
-- 'Setter'
---------------------------------------------------------------------

-- | A 'Setter' modifies part of a structure.
--
-- \( \mathsf{Setter}\;S\;A = \exists F : \mathsf{Functor}, S \equiv F\,A \)
--
type Setter s t a b = forall p. SetterLike p s t a b

type Setter' s a = Setter s s a a

type SetterLike p s t a b = Closed p => Distributive (Rep p) => TraversalLike p s t a b

type ASetter s t a b = Optic (Star Identity) s t a b

---------------------------------------------------------------------
-- 'Resetter'
---------------------------------------------------------------------

type Resetter s t a b = forall p. ResetterLike p s t a b

type Resetter' s a = Resetter s s a a

type ResetterLike p s t a b = Strong p => Cotraversal1Like p s t a b

type AResetter s t a b = Optic (Costar Identity) s t a b

---------------------------------------------------------------------
-- 'Conjoined'
---------------------------------------------------------------------

type Conjoined s t a b = forall p. ConjoinedLike p s t a b

type Conjoined' s a = Conjoined s s a a

type ConjoinedLike p s t a b = Representable p => Corepresentable p => Strong p => Comonad (Corep p) => Closed p => Distributive (Rep p) => Choice p => Optic p s t a b

type ConjoinedLike' p s a = ConjoinedLike p s s a a

type AConjoined s t a b = Optic (Bistar Identity Identity) s t a b


-- | TODO: Document
--
aresetter :: ((a -> b) -> s -> t) -> AResetter s t a b
aresetter sec = between Costar runCostar $ \f -> sec (f . Identity) . runIdentity



closed' :: Corepn (c -> a) (c -> b) a b
closed' = lower cotraverse

-- | TODO: Document
--
lifting :: F.Representable (Rep p) => ((a -> b) -> s -> t) -> RepnLike p s t a b
lifting f = lift $ genMap' f

genMap' :: F.Representable f => ((a -> b) -> s -> t) -> (a -> f b) -> s -> f t
genMap' f afb s = F.tabulate $ \i -> f (flip F.index i . afb) s

--applied :: Grate a (b -> c) (a , b) c
--appliedl :: Grid (a -> b, a) c b c
--appliedl = puncurry . closed
 
---------------------------------------------------------------------
-- 'Equality' 
---------------------------------------------------------------------

-- 'simple' is occasionally useful to constraint excessive polymorphism, 
-- e.g turn Optic into simple Optic'.
-- | @foo . (simple :: As Int) . bar@.
simple :: As a
simple = id

---------------------------------------------------------------------
-- 'Re' 
---------------------------------------------------------------------

-- | Turn a 'Lens', 'Prism' or 'Iso' around to build its dual.
--
-- If you have an 'Iso', 'from' is a more powerful version of this function
-- that will return an 'Iso' instead of a mere 'View'.
--
-- >>> 5 ^.re _Left
-- Left 5
--
-- >>> 6 ^.re (_Left.unto succ)
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

--The 'Re' type, and its instances witness the symmetry between the parameters of a 'Profunctor'.

newtype Re p s t a b = Re { runRe :: p b a -> p t s }

instance Profunctor p => Profunctor (Re p s t) where
    dimap f g (Re p) = Re (p . dimap g f)

instance Cochoice p => Choice (Re p s t) where
    right' (Re p) = Re (p . unright)

instance Costrong p => Strong (Re p s t) where
    first' (Re p) = Re (p . unfirst)

instance Choice p => Cochoice (Re p s t) where
    unright (Re p) = Re (p . pright)

instance Strong p => Costrong (Re p s t) where
    unfirst (Re p) = Re (p . pfirst)

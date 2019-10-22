{-# LANGUAGE UndecidableInstances, UndecidableSuperClasses, TypeOperators , GADTs, DataKinds, KindSignatures, TypeFamilies #-}

{-# LANGUAGE ExistentialQuantification #-}

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE QuantifiedConstraints #-}
-- {-# LANGUAGE IncoherentInstances #-}
-- {-# LANGUAGE OverlappingInstances #-}


module Data.Profunctor.Optic.Type (
    -- * Optics
    Optic, Optic', Equality, Equality'
    -- * Isos
  , Iso, Iso'
    -- * Lenses & Colenses
  , Lens, Lens', LensLike, LensLike', Colens, Colens', ColensLike, ColensLike'
    -- * Prisms & Coprisms
  , Prism, Prism', PrismLike, PrismLike', Coprism, Coprism', CoprismLike, CoprismLike'
    -- * Grates
  , Grate, Grate', GrateLike, GrateLike'
    -- * Grids
  , Grid, Grid', GridLike, GridLike'
    -- * Glasses
  , Glass, Glass', GlassLike, GlassLike'
    -- * Affine traversals
  , Traversal0, Traversal0', Traversal0Like, Traversal0Like'
    -- * Non-empty traversals
  , Traversal1, Traversal1', Traversal1Like, Traversal1Like'
    -- * General traversals
  , Traversal, Traversal', TraversalLike, TraversalLike', ATraversal, ATraversal'
    -- * Cotraversals
  , Cotraversal, Cotraversal', CotraversalLike, CotraversalLike'
    -- * Affine folds
  , Fold0, Fold0Like
    -- * Non-empty folds
  , Fold1, Fold1Like, AFold1
    -- * General folds
  , Fold, FoldLike, FoldRep, AFold
    -- * Unfolds  
  , Unfold, UnfoldRep, AUnfold
    -- * Getters
  , Getter, AGetter, PrimGetter, PrimGetterLike
    -- * Reviews
  , Review, AReview, PrimReview, PrimReviewLike
    -- * Setters
  , Setter, Setter', SetterLike, ASetter, AResetter 
    -- * Representable & Coreprestable profunctors
  , Over, Over', Under, Under'
    -- * 'Re'
  , Re(..)
  , module Export
) where

import Data.Semigroup (First, Last)
import Data.Profunctor.Optic.Prelude

import qualified Data.Profunctor.Optic.Type.VL as VL
import           Control.Applicative
import           Control.Monad
import           Control.Monad.Fix
import           Data.Bifoldable
import           Data.Bitraversable
import           Data.Coerce
import           Data.Data
import           Data.Distributive
import Data.Functor.Classes
import Data.Functor.Apply (Apply(..))

import GHC.Generics (Generic)
import Data.Int
import Data.Word
import Data.Functor.Base (NonEmptyF(..))
import Data.Traversable

import Data.Bifunctor as Export (Bifunctor (..))

---------------------------------------------------------------------
-- 'Optic'
---------------------------------------------------------------------

--type Optic p s t a b = Profunctor p => p a b -> p s t
--type Optical p s t a b = p a b -> p s t

type Optic p s t a b = p a b -> p s t

type Optic' p s a = Optic p s s a a

type Equality s t a b = forall p. Optic p s t a b 

type Equality' s a = Equality s s a a

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

type Colens s t a b = forall p. ColensLike p s t a b

type Colens' s a = Colens s s a a

type ColensLike p s t a b = Costrong p => Optic p s t a b

type ColensLike' p s a = ColensLike p s s a a

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

type Coprism s t a b = forall p. CoprismLike p s t a b

type Coprism' s a = Coprism s s a a

type CoprismLike p s t a b = Cochoice p => Optic p s t a b

type CoprismLike' p s a = CoprismLike p s s a a

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
-- 'Glass'
---------------------------------------------------------------------

-- | Glasses arise from the combination of prisms and grates.
--
-- \( \mathsf{Glass}\;S\;A = \exists D,I, S \cong D + (I \to A) \)
--
type Glass s t a b = forall p. GlassLike p s t a b

type Glass' s a = Glass s s a a

type GlassLike p s t a b = Closed p => PrismLike p s t a b

type GlassLike' p s a = GlassLike p s s a a

---------------------------------------------------------------------
-- 'Traversal0'
---------------------------------------------------------------------

-- | A 'Traversal0' processes at most one element, with no interactions.
--
-- \( \mathsf{Traversal0}\;S\;A = \exists C, D, S \cong D + C \times A \)
--
type Traversal0 s t a b = forall p. Traversal0Like p s t a b

type Traversal0' s a = Traversal0 s s a a

type Traversal0Like p s t a b = Choice p => LensLike p s t a b

type Traversal0Like' p s a = Traversal0Like p s s a a

---------------------------------------------------------------------
-- 'Traversal1'
---------------------------------------------------------------------

-- | A 'Traversal1' processes 1 or more elements, with non-empty applicative interactions.
--
type Traversal1 s t a b = forall p. Traversal1Like p s t a b

type Traversal1' s a = Traversal1 s s a a

type Traversal1Like p s t a b = (forall x. Apply (p x)) => Traversal0Like p s t a b

type Traversal1Like' p s a = Traversal1Like p s s a a

---------------------------------------------------------------------
-- 'Traversal'
---------------------------------------------------------------------

-- | A 'Traversal' processes 0 or more elements, with applicative interactions.
--
type Traversal s t a b = forall p. TraversalLike p s t a b

type Traversal' s a = Traversal s s a a

--type TraversalLike p s t a b = (forall x. Applicative (p x)) => Traversal0Like p s t a b
type TraversalLike p s t a b = Traversing p => Traversal0Like p s t a b

type TraversalLike' p s a = TraversalLike p s s a a

type ATraversal f s t a b = Applicative f => Optic (Star f) s t a b

type ATraversal' f s a = ATraversal f s s a a

---------------------------------------------------------------------
-- 'Cotraversal'
--------------------------------------------------------------------- 

type Cotraversal s t a b = forall p. Distributive (Corep p) => Under p s t a b
--type Cotraversal s t a b = forall p. CotraversalLike p s t a b

type Cotraversal' s a = Cotraversal s s a a

--(forall x. Coapplicative (p x))
type CotraversalLike p s t a b = (forall x. Distributive (p x)) => GridLike p s t a b

type CotraversalLike' p s a = CotraversalLike p s s a a

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
-- 'Unfold'
---------------------------------------------------------------------

--type Unfold t b = forall p. Distributive (Corep p) => Contravariant (Corep p) => Under' p t b
type Unfold t b = forall p. Bifunctor p => CotraversalLike p t t b b

type UnfoldRep r = Costar (Const r)

type AUnfold r t b = Optic' (UnfoldRep r) t b

---------------------------------------------------------------------
-- 'Getter'
---------------------------------------------------------------------

-- | A 'Getter' extracts exactly one result.
--
type Getter s a = forall p. (forall x. Contravariant (p x)) => LensLike p s s a a

type PrimGetter s t a b = forall p. PrimGetterLike p s t a b

type PrimGetterLike p s t a b = Profunctor p => (forall x. Contravariant (p x)) => Optic p s t a b

type AGetter s a = Optic' (FoldRep a) s a

---------------------------------------------------------------------
-- 'Review'
---------------------------------------------------------------------

-- | A 'Review' produces a result.
type Review t b = forall p. Bifunctor p => PrismLike p t t b b

type PrimReview s t a b = forall p. PrimReviewLike p s t a b

type PrimReviewLike p s t a b = Profunctor p => Bifunctor p => Optic p s t a b 

type AReview t b = Optic' (UnfoldRep b) t b

---------------------------------------------------------------------
-- 'Setter'
---------------------------------------------------------------------


-- | A 'Setter' modifies part of a structure.
--
-- \( \mathsf{Setter}\;S\;A = \exists F : \mathsf{Functor}, S \equiv F\,A \)
--
--type Setter s t a b = forall p. Distributive (Rep p) => Over p s t a b
type SetterLike p s t a b = Mapping p => Closed p => (forall x. Distributive (p x)) => TraversalLike p s t a b
--type SetterLike p s t a b = Choice p => CotraversalLike p s t a b

--type SetterLike p s t a b = Mapping p => Over p s t a b
type Setter s t a b = forall p. SetterLike p s t a b
--type Setter s t a b = Optic (->) s t a b

type Setter' s a = Setter s s a a

-- type SetterLike p s t a b = Closed p => (forall x. Distributive (p x)) => TraversalLike p s t a b
-- type SetterLike p s t a b = Choice p => CotraversalLike p s t a b
-- type Setter s t a b = Category p => Closed p => 
-- type Setter s t a b = Optic (->) s t a b

type ASetter s t a b = Optic (Star Identity) s t a b

type AResetter s t a b = Optic (Costar Identity) s t a b


---------------------------------------------------------------------
-- 'Over' & 'Under'
---------------------------------------------------------------------

type Over p s t a b = Representable p => Optic p s t a b

type Over' p s a = Representable p => Optic p s s a a

type Under p s t a b = Corepresentable p => Optic p s t a b

type Under' p s a = Under p s s a a

overLike :: ((a -> b) -> s -> t) -> ASetter s t a b
overLike sec = between Star runStar $ \f -> Identity . sec (runIdentity . f)

-- | TODO: Document
--
underLike :: ((a -> b) -> s -> t) -> AResetter s t a b
underLike sec = between Costar runCostar $ \f -> sec (f . Identity) . runIdentity

-- | TODO: Document
--
cloneOver :: Optic (Star (Rep p)) s t a b -> Over p s t a b
cloneOver = between fromStar star 

-- | TODO: Document
--
cloneUnder :: Optic (Costar (Corep p)) s t a b -> Under p s t a b
cloneUnder = between fromCostar costar 

closed' :: Under p (c -> a) (c -> b) a b
closed' = lower cotraverse


{-
type SLens s t a b = forall p. Strong p => PSemigroup (,) p => Optic p s t a b
type SLens' s a = SLens s s a a

--v2 :: Semigroupal p => Optic p (V2 a) (V2 b) a b
v2 :: SLens (V2 a) (V2 b) a b
v2 p = dimap (\(V2 x y) -> (x, y)) (\(x, y) -> V2 x y) (p *** p)

-- >>>  contents skipLast (1,2,3)
-- [1,2]
skipLast :: SLens (a, a, c) (b, b, c) a b
skipLast p = dimap group ungroup (first' (p *** p)) where
  group  (x, y, z) = ((x, y), z)
  ungroup ((x, y), z) = (x, y, z)

skipLast' :: SLens' (V3 a) a
skipLast' p = dimap group ungroup (first' (p *** p)) where
  group  (V3 x y z) = ((x, y), z)
  ungroup ((x, y), z) = V3 x y z


v4 :: SLens (V4 a) (V4 b) a b
v4 p = dimap (\(V4 x y z w) -> (x, (y, (z, w)))) (\(x, (y, (z, w))) -> V4 x y z w) (p *** p *** p *** p)
-}

{-λ> review (v2 . right' . _V2) 1 :: V2 (Either Bool (V2 Int))
V2 (Right (V2 1 1)) (Right (V2 1 1))
and zipWithOf:

λ> let as = V2 (Left ())     (Right (1,2))
λ> let bs = V2 (Right (3,4)) (Right (5,6))
λ> zipWithOf (v2 . right' . first') (,) as bs
V2 (Left ()) (Right ((1,5),2))
But also traverseOf:

λ> let f x = state (\s -> (x + s, s +1))
λ> evalState (traverseOf v2 f (V2 5 7)) 1
V2 6 9
and toListOf:

λ> toListOf (v2 . v2) (V2 (V2 1 2) (V2 3 4))
[1,2,3,4]

-}

---------------------------------------------------------------------
-- 'Re'
---------------------------------------------------------------------


--The 'Re' type, and its instances witness the symmetry between the parameters of a 'Profunctor'. 

newtype Re p s t a b = Re { runRe :: p b a -> p t s }

instance Profunctor p => Profunctor (Re p s t) where
    dimap f g (Re p) = Re (p . dimap g f)

instance Cochoice p => Choice (Re p s t) where
    right' (Re p) = Re (p . unright)

instance Costrong p => Strong (Re p s t) where
    first' (Re p) = Re (p . unfirst)

instance Choice p => Cochoice (Re p s t) where
    unright (Re p) = Re (p . right')

instance Strong p => Costrong (Re p s t) where
    unfirst (Re p) = Re (p . first')

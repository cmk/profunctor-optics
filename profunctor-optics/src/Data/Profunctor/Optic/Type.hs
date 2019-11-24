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
  , Ix, IndexedOptic, IndexedOptic'
  , Cx, CoindexedOptic, CoindexedOptic'
    -- * Equality
  , Equality, Equality', As
    -- * Isos
  , Iso, Iso'
    -- * Lenses & Relenses
  , Lens, Lens', Ixlens, Ixlens', Relens, Relens', Rxlens, Rxlens'
    -- * Prisms & Reprisms
  , Prism, Prism', Ixprism, Ixprism', Reprism, Reprism', Rxprism, Rxprism' 
    -- * Grates
  , Grate, Grate', Cxgrate, Cxgrate'
    -- * Repns & Corepns
  , Repn  , Repn'  , RepnLike  , RepnLike'  , ARepn  , ARepn'
  , Ixrepn, Ixrepn', IxrepnLike, IxrepnLike', AIxrepn, AIxrepn'
  , Corepn, Corepn', CorepnLike, CorepnLike', ACorepn, ACorepn'
  , Cxrepn, Cxrepn', CxrepnLike, CxrepnLike', ACxrepn, ACxrepn'
    -- * Affine traversals, general & non-empty traversals, & cotraversals
  , Traversal0 , Traversal0'                               , Ixtraversal0, Ixtraversal0'
  , Traversal  , Traversal'   , ATraversal  , ATraversal'  , Ixtraversal , Ixtraversal'
  , Traversal1 , Traversal1'  , ATraversal1 , ATraversal1'
  , Cotraversal, Cotraversal' , ACotraversal, ACotraversal', Cxtraversal , Cxtraversal'

      -- * Affine folds, general & non-empty folds, & cofolds
  , Fold0, FoldRep, Fold, AFold, Ixfold, AIxfold, Fold1, AFold1
  , Cofold, CofoldRep, ACofold
    -- * Views & Reviews
  , PrimView  , APrimView  , View  , AView  , Ixview, AIxview
  , PrimReview, APrimReview, Review, AReview, Cxview, ACxview
    -- * Setters & Resetters
  , Setter  , Setter'  , ASetter  , ASetter'  , Ixsetter, AIxsetter
  , Resetter, Resetter', AResetter, AResetter', Cxsetter, ACxsetter
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

-- | Generic type for an indexed optic.
type Ix p i a b = p (i , a) b

-- | Generic type for a co-indexed optic.
type Cx p k a b = p a (k -> b)

type IndexedOptic p i s t a b = p (i , a) b -> p (i , s) t

type IndexedOptic' p i s a = IndexedOptic p i s s a a

type CoindexedOptic p k s t a b = p a (k -> b) -> p s (k -> t) 

type CoindexedOptic' p k s a = CoindexedOptic p k s s a a

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
type Lens s t a b = forall p. Strong p => Optic p s t a b

type Lens' s a = Lens s s a a

type Ixlens i s t a b = forall p. Strong p => IndexedOptic p i s t a b 

type Ixlens' i s a = Ixlens i s s a a 

type Relens s t a b = forall p. Costrong p => Optic p s t a b 

type Relens' s a = Relens s s a a

type Rxlens r s t a b = forall p. Costrong p => IndexedOptic p r s t a b 

type Rxlens' r s a = Rxlens r s s a a 

---------------------------------------------------------------------
-- 'Prism' & 'Reprism'
---------------------------------------------------------------------

-- | Prisms access one piece of a sum.
--
-- \( \mathsf{Prism}\;S\;A = \exists D, S \cong D + A \)
--
type Prism s t a b = forall p. Choice p => Optic p s t a b 

type Prism' s a = Prism s s a a

type Ixprism i s t a b = forall p. Choice p => IndexedOptic p i s t a b 

type Ixprism' i s a = Ixprism i s s a a

type Reprism s t a b = forall p. Cochoice p => Optic p s t a b 

type Reprism' t b = Reprism t t b b 

type Rxprism r s t a b = forall p. Cochoice p => IndexedOptic p r s t a b

type Rxprism' r s a = Reprism s s a a

---------------------------------------------------------------------
-- 'Grate'
---------------------------------------------------------------------

-- | Grates access the codomain of a function.
--
--  \( \mathsf{Grate}\;S\;A = \exists I, S \cong I \to A \)
--
type Grate s t a b = forall p. Closed p => Optic p s t a b 

type Grate' s a = Grate s s a a

type Cxgrate k s t a b = forall p. Closed p => CoindexedOptic p k s t a b 

type Cxgrate' k s a = Cxgrate k s s a a

---------------------------------------------------------------------
-- 'Repn' & 'Corepn'
---------------------------------------------------------------------

type Repn s t a b = forall p. RepnLike p s t a b

type Repn' s a = Repn s s a a

type RepnLike p s t a b = Representable p => Optic p s t a b

type RepnLike' p s a = RepnLike p s s a a

type ARepn f s t a b = Optic (Star f) s t a b

type ARepn' f s a = ARepn f s s a a

type Ixrepn i s t a b = forall p. IxrepnLike p i s t a b 

type Ixrepn' i s a = Ixrepn i s s a a

type IxrepnLike p i s t a b = Representable p => IndexedOptic p i s t a b

type IxrepnLike' p i s a = IxrepnLike p i s s a a

type AIxrepn f i s t a b = IndexedOptic (Star f) i s t a b

type AIxrepn' f i s a = AIxrepn f i s s a a 

type Corepn s t a b = forall p. CorepnLike p s t a b

type Corepn' s a = Corepn s s a a

type CorepnLike p s t a b = Corepresentable p => Optic p s t a b

type CorepnLike' p t b = CorepnLike p t t b b 

type ACorepn f s t a b = Optic (Costar f) s t a b

type ACorepn' f t b = ACorepn f t t b b

type Cxrepn k s t a b = forall p. CxrepnLike p k s t a b

type Cxrepn' k t b = Cxrepn k t t b b

type CxrepnLike p k s t a b = Corepresentable p => CoindexedOptic p k s t a b

type CxrepnLike' p k t b = CxrepnLike p k t t b b

type ACxrepn f k s t a b = CoindexedOptic (Costar f) k s t a b

type ACxrepn' f k t b = ACxrepn f k t t b b

---------------------------------------------------------------------
-- 'Traversal0', 'Traversal' , 'Traversal1', & 'Cotraversal'
---------------------------------------------------------------------

-- | A 'Traversal0' processes at most one part of the whole, with no interactions.
--
-- \( \mathsf{Traversal0}\;S\;A = \exists C, D, S \cong D + C \times A \)
--
type Traversal0 s t a b = forall p. Strong p => Choice p => Optic p s t a b 

type Traversal0' s a = Traversal0 s s a a

type Ixtraversal0 i s t a b = forall p. Strong p => Choice p => IndexedOptic p i s t a b 

type Ixtraversal0' i s a = Ixtraversal0 i s s a a 

-- | A 'Traversal' processes 0 or more parts of the whole, with 'Applicative' interactions.
--
-- \( \mathsf{Traversal}\;S\;A = \exists F : \mathsf{Traversable}, S \equiv F\,A \)
--
type Traversal s t a b = forall p. Choice p => Applicative (Rep p) => RepnLike p s t a b

type Traversal' s a = Traversal s s a a

type Ixtraversal i s t a b = forall p. Choice p => Applicative (Rep p) => IxrepnLike p i s t a b 

type Ixtraversal' i s a = Ixtraversal i s s a a

type ATraversal f s t a b = Applicative f => ARepn f s t a b

type ATraversal' f s a = ATraversal f s s a a

-- | A 'Traversal1' processes 1 or more parts of the whole, with 'Apply' interactions.
--
-- \( \mathsf{Traversal1}\;S\;A = \exists F : \mathsf{Traversable1}, S \equiv F\,A \)
--
type Traversal1 s t a b = forall p. Choice p => Apply (Rep p) => RepnLike p s t a b 

type Traversal1' s a = Traversal1 s s a a

type ATraversal1 f s t a b = Apply f => ARepn f s t a b

type ATraversal1' f s a = ATraversal1 f s s a a

type Cotraversal s t a b = forall p. Closed p => Choice p => ComonadApply (Corep p) => CorepnLike p s t a b 

type Cotraversal' s a = Cotraversal s s a a

type ACotraversal f s t a b = ComonadApply f => ACorepn f s t a b

type ACotraversal' f s a = ACotraversal f s s a a

type Cxtraversal k s t a b = forall p. Closed p => Choice p => ComonadApply (Corep p) => CxrepnLike p k s t a b 

type Cxtraversal' k t b = Cxtraversal k t t b b 

---------------------------------------------------------------------
-- 'Fold0', 'Fold', 'Fold1' & 'Cofold'
---------------------------------------------------------------------

-- | A 'Fold0' combines at most one element, with no interactions.
--
type Fold0 s a = forall p. (forall x. Contravariant (p x)) => Strong p => Choice p => Optic' p s a 

-- | A 'Fold' combines 0 or more elements, with 'Monoid' interactions.
--
type Fold s a = forall p. (forall x. Contravariant (p x)) => Choice p => Applicative (Rep p) => RepnLike' p s a

type FoldRep r = Star (Const r)

type AFold r s a = Optic' (FoldRep r) s a

type Ixfold i s a = forall p. (forall x. Contravariant (p x)) => Choice p => Applicative (Rep p) => IxrepnLike' p i s a

type AIxfold r i s a = IndexedOptic' (FoldRep r) i s a

-- | A 'Fold1' combines 1 or more elements, with 'Semigroup' interactions.
--
type Fold1 s a = forall p. (forall x. Contravariant (p x)) => Choice p => Apply (Rep p) => RepnLike p s s a a 

type AFold1 r s a = Optic' (FoldRep r) s a

type Cofold t b = forall p. Bifunctor p =>  Closed p => Choice p => ComonadApply (Corep p) => CorepnLike p t t b b

type CofoldRep r = Costar (Const r)

type ACofold r t b = Optic' (CofoldRep r) t b

---------------------------------------------------------------------
-- 'View' & 'Review'
---------------------------------------------------------------------

type PrimView s t a b = forall p. Profunctor p => (forall x. Contravariant (p x)) => Optic p s t a b

type APrimView r s t a b = Optic (FoldRep r) s t a b

type View s a = forall p. Strong p => (forall x. Contravariant (p x)) => Optic' p s a 

type AView s a = Optic' (FoldRep a) s a

type Ixview i s a = forall p. Strong p => (forall x. Contravariant (p x)) => IndexedOptic' p i s a

type AIxview i s a = IndexedOptic' (FoldRep (Maybe i , a)) i s a

type PrimReview s t a b = forall p. Profunctor p => Bifunctor p => Optic p s t a b

type APrimReview s t a b = Optic Tagged s t a b

type Review t b = forall p. Costrong p => Bifunctor p => Optic' p t b

type AReview t b = Optic' Tagged t b

type Cxview k t b = forall p. Costrong p => Bifunctor p => CoindexedOptic' p k t b

type ACxview k t b = CoindexedOptic' Tagged k t b

---------------------------------------------------------------------
-- 'Setter' & 'Resetter'
---------------------------------------------------------------------

-- | A 'Setter' modifies part of a structure.
--
-- \( \mathsf{Setter}\;S\;A = \exists F : \mathsf{Functor}, S \equiv F\,A \)
--
type Setter s t a b = forall p. Closed p => Choice p => Applicative (Rep p) => Distributive (Rep p) => RepnLike p s t a b

type Setter' s a = Setter s s a a

type ASetter s t a b = ARepn Identity s t a b

type ASetter' s a = ASetter s s a a 

type Ixsetter i s t a b = forall p. Closed p => Choice p => Applicative (Rep p) => Distributive (Rep p) => IxrepnLike p i s t a b

type Ixsetter' i s a = Ixsetter i s s a a 

type AIxsetter i s t a b = AIxrepn Identity i s t a b

type Resetter s t a b = forall p. Strong p => Closed p => Choice p => ComonadApply (Corep p) => Traversable (Corep p) => CorepnLike p s t a b 

type Resetter' s a = Resetter s s a a

type AResetter s t a b = ACorepn Identity s t a b

type AResetter' s a = AResetter s s a a

type Cxsetter k s t a b = forall p. Strong p => Closed p => Choice p => ComonadApply (Corep p) => Traversable1 (Corep p) => CxrepnLike p k s t a b

type ACxsetter k s t a b = ACxrepn Identity k s t a b

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
-- 're' . 're'  ≡ id
-- @
--
-- @
-- 're' :: 'Iso' s t a b   -> 'Iso' b a t s
-- 're' :: 'Lens' s t a b  -> 'Relens' b a t s
-- 're' :: 'Prism' s t a b -> 'Reprism' b a t s
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

---------------------------------------------------------------------
-- Orphan instances 
---------------------------------------------------------------------

instance Apply f => Apply (Star f a) where
  Star ff <.> Star fx = Star $ \a -> ff a <.> fx a

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

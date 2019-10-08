{-# LANGUAGE UndecidableSuperClasses, TypeOperators , GADTs, DataKinds, KindSignatures, TypeFamilies #-}

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
    module Data.Profunctor.Optic.Type
  , module VL
  , module Export
) where

import Data.Semigroup (First, Last)
--import Data.Profunctor.Optic.Type.Class 
import Data.Profunctor.Optic.Prelude

import qualified Data.Profunctor.Optic.Type.VL as VL
import           Control.Applicative
import           Control.Monad
import           Control.Monad.Fix
import           Data.Bifoldable
import Data.Bifunctor as Export (Bifunctor (..))
import           Data.Bitraversable
import           Data.Coerce
import           Data.Data
import           Data.Distributive
import Data.Functor.Classes

type Optic p s t a b = p a b -> p s t

type Optic' p s a = Optic p s s a a

type Equality s t a b = forall f g. IsoLike f g s t a b 

type Equality' s a = Equality s s a a

type Iso s t a b = forall p. Profunctor p => Optic p s t a b

type Iso' s a = Iso s s a a

type IsoVL s t a b = forall f g. Functor f => Functor g => IsoLike f g s t a b

type IsoVL' s a = IsoVL s s a a 

type IsoLike f g s t a b = Optic (Bistar f g) s t a b

type Over p s t a b = Representable p => Optic p s t a b

type Over' p s a = Representable p => Optic p s s a a

type OverLike f s t a b = Optic (Star f) s t a b

type OverLike' f s a = OverLike f s s a a

type Under p s t a b = Corepresentable p => Optic p s t a b

type Under' p s a = Under p s s a a

type UnderLike g s t a b = Optic (Costar g) s t a b

type UnderLike' g s a = UnderLike g s s a a

-- * 

type Lens s t a b = forall p. Strong p => Optic p s t a b

type Lens' s a = Lens s s a a

type LensVL s t a b = forall f. Functor f => OverLike f s t a b

type LensVL' s a = LensVL s s a a

type Prism s t a b = forall p. Choice p => Optic p s t a b

type Prism' s a = Prism s s a a

type PrismVL s t a b = forall f g. Applicative f => Traversable g => IsoLike f g s t a b

type PrismVL' s a = PrismVL s s a a 

type Grate s t a b = forall p. Closed p => Optic p s t a b

type Grate' s a = Grate s s a a

type GrateVL s t a b = forall g. Functor g => UnderLike g s t a b

type GrateVL' s a = GrateVL s s a a

-- A 'Affine' extracts at most one result, with no monoidal interactions.
type Affine s t a b = forall p. Strong p => Choice p => Optic p s t a b

type Affine' s a = Affine s s a a

--type Foo s t a b = forall p. Closed p => Strong p => Optic p s t a b

--type Bar s t a b = forall p. Choice p => Closed p => Optic p s t a b

-- *


type Traversal s t a b = forall p. Applicative (Rep p) => Over p s t a b

type Traversal' s a = Traversal s s a a

--type CotraversalVL s t a b = forall f g. (Applicative f, Functor g) => AdapterLike f g s t a b
type Cotraversal s t a b = forall p. Distributive (Corep p) => Under p s t a b

-- A 'Traversal1' extracts at least one result.
--type Traversal1 s t a b = forall p. Traversing1 p => Optic p s t a b

--type Traversal1' s a = Traversal1 s s a a

--type Fold s a = forall p. (forall x. Contravariant (p x), Traversing p) => Optic' p s a
--type Fold s a = forall p. RPhantom p => Strong p => Optic' p s a
type Fold s a = forall p. Applicative (Rep p) => Contravariant (Rep p) => Over' p s a

type FoldLike r s a = OverLike' (Const r) s a

-- A 'Fold0' extracts at most one result.
type Fold0 s a = forall p. Choice p => Contravariant (Rep p) => Over' p s a

type Unfold t b = forall p. Distributive (Corep p) => Contravariant (Corep p) => Under' p t b

type UnfoldLike r t b = UnderLike' (Const r) t b

-- A 'AffineUnfold' extracts at least one result. should be able to do this w/ a UnderLike / Cotraversal
type AffineUnfold t b = forall p. Strong p => Contravariant (Corep p) => Under' p t b

type PrimGetter s t a b = forall p. Contravariant (Rep p) => Over p s t a b

type PrimGetter' s a = PrimGetter s s a a

type PrimReview s t a b = forall p. Contravariant (Corep p) => Under p s t a b

type PrimReview' t b = PrimReview t t b b

-- A 'Getter' extracts exactly one result.
--type Getter s a = forall p . Strong p => Representable p => Contravariant (Rep p) => p a b -> p s t
type Getter s a = forall p. Strong p => Contravariant (Rep p) => Over' p s a

type Review t b = forall p. Choice p => Contravariant (Corep p) => Under' p t b




-- * Setter

type Setter s t a b = forall p. Representable p => Distributive (Rep p) => Optic p s t a b
--type SetterVL s t a b = forall f. F.Representable f => OverLike f s t a b

type Setter' s a = Setter s s a a

--type Resetter s t a b = forall p. Corepresentable p => Applicative (Corep p) => Optic p s t a b
--type ResetterVL s t a b = forall f. Representable f => Applicative f => UnderLike f s t a b

--type Resetter' s a = Resetter s s a a
type ASetter s t a b = OverLike Identity s t a b

type AResetter s t a b = UnderLike Identity s t a b





{-
toOverLike :: AdapterLike f Identity s t a b -> OverLike f s t a b
toOverLike o h = lower' o h runIdentity Identity -- l f = l (f . runIdentity) . Identity 

--fromOverLike :: AdapterLike f Identity s t a b -> OverLike f s t a b
--fromOverLike o h = lower o h Identity runIdentity 

toOverLike' o h = lower' o h getConst Const 

toUnderLike :: AdapterLike Identity g s t a b -> UnderLike g s t a b
toUnderLike o h = colower o h runIdentity Identity

toUnderLike' o h = colower o h getConst Const


lift :: OverLike f s t a b -> AdapterLike f Identity s t a b
lift l f = l (f . Identity) . runIdentity
-}


--fromGrate :: UnderLike g s t a b -> Optic (Costar g) s t a b

--fromLens :: OverLike f s t a b -> Optic (Star f) s t a b


--alternated :: forall f s a. (forall f. Alternative f) => Star f s a -> Traversal s a s a
--alternated f = between runStar $ Star . (<||> f)
--alternated (Star f) = wander (<||> f)



---------------------------------------------------------------------
-- 'Re'
---------------------------------------------------------------------


--The 'Re' type, and its instances witness the symmetry of 'Profunctor' 
-- and the relation between 'InPhantom' and 'OutPhantom'.

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

---------------------------------------------------------------------
-- 'Zipped'
---------------------------------------------------------------------


newtype Zipped a b = Zipped { runZipped :: a -> a -> b }

instance Profunctor Zipped where
    dimap f g (Zipped p) = Zipped (\x y -> g (p (f x) (f y)))

instance Closed Zipped where
    closed (Zipped p) = Zipped (\f g x -> p (f x) (g x))

instance Choice Zipped where
    right' (Zipped p) = Zipped (\x y -> p <$> x <*> y)

instance Strong Zipped where
    first' (Zipped p) = Zipped (\(x, c) (y, _) -> (p x y, c))

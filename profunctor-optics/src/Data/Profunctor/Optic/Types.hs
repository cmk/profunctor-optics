{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE QuantifiedConstraints #-}

#ifndef MIN_VERSION_profunctors
#define MIN_VERSION_profunctors(x,y,z) 1
#endif

module Data.Profunctor.Optic.Types (
    -- * Optic, IndexedOptic, & CoindexedOptic
    Optic, Optic'
  , IndexedOptic, IndexedOptic'
  , CoindexedOptic, CoindexedOptic'
    -- * Iso & Equality
  , Iso, Iso', Equality, Equality'
    -- * Lens
  , Lens, Lens', Ixlens, Ixlens'
    -- * Prism
  , Prism, Prism', Cxprism, Cxprism'
    -- * Grate
  , Grate, Grate', Cxgrate, Cxgrate'
    -- * Affine & Option
  , Affine, Affine', Ixaffine, Ixaffine'
  , Option, Ixoption
    -- * Grism
  , Grism , Grism'
    -- * Traversal, Traversal1, Fold & Fold1
  , Traversal    , Traversal'   , Ixtraversal , Ixtraversal'
  , Traversal1   , Traversal1'  , Ixtraversal1, Ixtraversal1'
  , Fold, Ixfold , Fold1, Ixfold1
    -- * Cotraversal
  , Cotraversal  , Cotraversal'
    -- * View & Review
  , PrimView, View, Ixview, PrimReview, Review, Cxview
    -- * Setter & Resetter
  , Setter, Setter', Ixsetter, Ixsetter'
  , Resetter, Resetter', Cxsetter, Cxsetter'
    -- * Coapplicative
  , Coapplicative(..), Branch(..)
  , between
    -- * 'Re'
  , Re(..), re
  , module Export
) where

import Data.Bifunctor (Bifunctor(..))
import Data.Functor.Apply (Apply(..))
import Data.Profunctor.Optic.Import hiding (branch)
import Data.Profunctor.Extra as Export (type (+))
import Data.Profunctor.Types as Export
import qualified Control.Arrow as A

import Data.List.NonEmpty as L1
import qualified Data.Bifunctor as B

-- $setup
-- >>> :set -XCPP
-- >>> :set -XNoOverloadedStrings
-- >>> :load Data.Profunctor.Optic

---------------------------------------------------------------------
-- Optic
---------------------------------------------------------------------

type Optic p s t a b = p a b -> p s t

type Optic' p s a = Optic p s s a a

type IndexedOptic p i s t a b = p (i , a) b -> p (i , s) t

type IndexedOptic' p i s a = IndexedOptic p i s s a a

type CoindexedOptic p k s t a b = p a (k -> b) -> p s (k -> t)

type CoindexedOptic' p k t b = CoindexedOptic p k t t b b

---------------------------------------------------------------------
-- Iso & Equality
---------------------------------------------------------------------

-- | 'Iso'
--
-- \( \mathsf{Iso}\;S\;A = S \cong A \)
--
type Iso s t a b = forall p. Profunctor p => Optic p s t a b

type Iso' s a = Iso s s a a

type Equality s t a b = forall p. Optic p s t a b

type Equality' s a = Equality s s a a

---------------------------------------------------------------------
-- Lens
---------------------------------------------------------------------

-- | Lenses access one piece of a product.
--
-- \( \mathsf{Lens}\;S\;A  = \exists C, S \cong C \times A \)
--
type Lens s t a b = forall p. Strong p => Optic p s t a b

type Lens' s a = Lens s s a a

type Ixlens i s t a b = forall p. Strong p => IndexedOptic p i s t a b 

type Ixlens' i s a = Ixlens i s s a a 

---------------------------------------------------------------------
-- Prism
---------------------------------------------------------------------

-- | Prisms access one piece of a sum.
--
-- \( \mathsf{Prism}\;S\;A = \exists D, S \cong D + A \)
--
type Prism s t a b = forall p. Choice p => Optic p s t a b

type Prism' s a = Prism s s a a

type Cxprism k s t a b = forall p. Choice p => CoindexedOptic p k s t a b

type Cxprism' k s a = Cxprism k s s a a

---------------------------------------------------------------------
-- Grate
---------------------------------------------------------------------

-- | Grates access the codomain of a function.
--
--  \( \mathsf{Grate}\;S\;A = \exists I, S \cong I \to A \)
--
type Grate s t a b = forall p. Closed p => Optic p s t a b 

type Grate' s a = Grate s s a a

type Cxgrate k s t a b = forall p. Closed p => CoindexedOptic p k s t a b 

type Cxgrate' k s a = Cxgrate k s s a a

type Colens s t a b = forall p. Costrong p => Optic p s t a b 

type Colens' s a = Colens s s a a

type Cxlens k s t a b = forall p. Costrong p => CoindexedOptic p k s t a b

type Cxlens' k s a = Cxlens k s s a a

type Cotraversal0 s t a b = forall p. (Choice p, Closed p) => Optic p s t a b

type Cotraversal0' t b = Cotraversal0 t t b b

---------------------------------------------------------------------
-- Affine & Option
---------------------------------------------------------------------

-- | A 'Affine' processes 0 or more parts of the whole, with no interactions.
--
-- \( \mathsf{Affine}\;S\;A = \exists C, D, S \cong D + C \times A \)
--
type Affine s t a b = forall p. (Choice p, Strong p) => Optic p s t a b 

type Affine' s a = Affine s s a a

type Ixaffine i s t a b = forall p. (Choice p, Strong p) => IndexedOptic p i s t a b 

type Ixaffine' i s a = Ixaffine i s s a a 

-- | A 'Option' combines at most one element, with no interactions.
--
type Option s a = forall p. (Choice p, Strong p, forall x. Contravariant (p x)) => Optic' p s a 

type Ixoption i s a = forall p. (Choice p, Strong p, forall x. Contravariant (p x)) => IndexedOptic' p i s a 

---------------------------------------------------------------------
-- Grism
---------------------------------------------------------------------

-- | https://en.wikipedia.org/wiki/Grism
--
type Grism s t a b = forall p. (Choice p, Closed p) => Optic p s t a b

type Grism' t b = Grism t t b b

---------------------------------------------------------------------
-- Traversal, Traversal1, Fold, & Fold1
---------------------------------------------------------------------

-- | A 'Traversal' processes 0 or more parts of the whole, with 'Applicative' interactions.
--
-- \( \mathsf{Traversal}\;S\;A = \exists F : \mathsf{Traversable}, S \equiv F\,A \)
--
type Traversal s t a b = forall p. (Choice p, Strong p, Representable p, Applicative (Rep p)) => Optic p s t a b

type Traversal' s a = Traversal s s a a

type Ixtraversal i s t a b = forall p. (Choice p, Strong p, Representable p, Applicative (Rep p)) => IndexedOptic p i s t a b 

type Ixtraversal' i s a = Ixtraversal i s s a a

-- | A 'Traversal1' processes 1 or more parts of the whole, with 'Apply' interactions.
--
-- \( \mathsf{Traversal1}\;S\;A = \exists F : \mathsf{Traversable1}, S \equiv F\,A \)
--
type Traversal1 s t a b = forall p. (Strong p, Representable p, Apply (Rep p)) => Optic p s t a b 

type Traversal1' s a = Traversal1 s s a a

type Ixtraversal1 i s t a b = forall p. (Strong p, Representable p, Apply (Rep p)) => IndexedOptic p i s t a b 

type Ixtraversal1' i s a = Ixtraversal1 i s s a a

type Cofold0 t b = forall p. (Choice p, Closed p, Strong p, forall x. Contravariant (p x)) => Optic' p t b 

-- | A 'Fold1' combines 1 or more elements, with 'Semigroup' interactions.
--
type Fold1 s a = forall p. (Strong p, Representable p, Apply (Rep p), forall x. Contravariant (p x)) => Optic' p s a 

type Ixfold1 i s a = forall p. (Strong p, Representable p, Apply (Rep p), forall x. Contravariant (p x)) => IndexedOptic' p i s a

-- | A 'Fold' combines 0 or more elements, with 'Monoid' interactions.
--
type Fold s a = forall p. (Choice p, Representable p, Applicative (Rep p), forall x. Contravariant (p x)) => Optic' p s a

type Ixfold i s a = forall p. (Choice p, Representable p, Applicative (Rep p), forall x. Contravariant (p x)) => IndexedOptic' p i s a

-- type Cofold t b = forall p. (Closed p, Corepresentable p, Coapplicative (Corep p), Bifunctor p) => Optic' p t b

---------------------------------------------------------------------
-- Cotraversal
---------------------------------------------------------------------

type Cotraversal s t a b = forall p. (Choice p, Closed p, Coapplicative (Corep p), Corepresentable p) => Optic p s t a b

type Cotraversal' t b = Cotraversal t t b b

---------------------------------------------------------------------
-- View & Review
---------------------------------------------------------------------

type PrimView s t a b = forall p. (Profunctor p, forall x. Contravariant (p x)) => Optic p s t a b

type View s a = forall p. (Strong p, forall x. Contravariant (p x)) => Optic' p s a 

type Ixview i s a = forall p. (Strong p, forall x. Contravariant (p x)) => IndexedOptic' p i s a

type PrimReview s t a b = forall p. (Profunctor p, Bifunctor p) => Optic p s t a b

type Review t b = forall p. (Closed p, Bifunctor p) => Optic' p t b

type Cxview k t b = forall p. (Closed p, Bifunctor p) => CoindexedOptic' p k t b

---------------------------------------------------------------------
-- Setter & Resetter
---------------------------------------------------------------------

-- | A 'Setter' modifies part of a structure.
--
-- \( \mathsf{Setter}\;S\;A = \exists F : \mathsf{Functor}, S \equiv F\,A \)
--
type Setter s t a b = forall p. (Choice p, Strong p, Representable p, Applicative (Rep p), Distributive (Rep p)) => Optic p s t a b

type Setter' s a = Setter s s a a

type Ixsetter i s t a b = forall p. (Choice p, Strong p, Representable p, Applicative (Rep p), Distributive (Rep p)) => IndexedOptic p i s t a b

type Ixsetter' i s a = Ixsetter i s s a a 

type Resetter s t a b = forall p. (Choice p, Closed p, Corepresentable p, Coapplicative (Corep p), Traversable (Corep p)) => Optic p s t a b 

type Resetter' s a = Resetter s s a a

type Cxsetter k s t a b = forall p. (Choice p, Closed p, Corepresentable p, Coapplicative (Corep p), Traversable (Corep p)) => CoindexedOptic p k s t a b

type Cxsetter' k t b = Cxsetter k t t b b 


---------------------------------------------------------------------
-- Branch & Coapplicative
---------------------------------------------------------------------

-- branch . fmap Left == Left 
-- branch . fmap Right == Right
-- (fmap Left ||| fmap Right) . branch == id

-- >>> (fmap Left ||| fmap Right) . branch $ (Left 1) :| [Right 2]
-- Left 1 :| []
--
class Functor f => Branch f where
  branch :: f (Either a b) -> Either (f a) (f b)

cobranch :: Apply f => (f a, f b) -> f (a, b)
cobranch = uncurry $ liftF2 (,)

instance Branch Identity where
  branch (Identity ab) = either (Left . Identity) (Right . Identity) ab

{-
instance Branch (Const r) where branch (Const r) = Right (Const r)
-}

instance Branch (Tagged k) where
  branch (Tagged ab) = either (Left . Tagged) (Right . Tagged) ab

instance Branch ((,) r) where
  branch (r, a) = either (Left . (r,)) (Right . (r,)) a

instance Monoid m => Branch ((->) m) where
  branch f = either (Left . const) (Right . const) $ f mempty

instance Branch NonEmpty where
  branch (Left x :| zs) = Left $ x :| foldr (either (:) (const id)) [] zs
  branch (Right y :| zs) = Right $ y :| foldr (either (const id) (:)) [] zs

instance (Branch f, Branch g) => Branch (Compose f g) where
  branch (Compose ab) = B.bimap Compose Compose . branch . fmap branch $ ab

class Branch f => Coapplicative f where
  -- either (f . copure) (g . copure) . branch == either f g . copure
  copure :: f a -> a

instance Coapplicative Identity where
  copure (Identity a) = a

instance Coapplicative (Tagged k) where
  copure (Tagged a) = a

instance Coapplicative ((,) r) where
  copure (_, a) = a

instance Monoid m => Coapplicative ((->) m) where
  copure f = f mempty

instance Coapplicative NonEmpty where
  copure = L1.head

catLefts :: [Either a b] -> [a]
catLefts = foldr (either (:) (const id)) []

catRights :: [Either a b] -> [b]
catRights = foldr (either (const id) (:)) []

instance (Coapplicative f, Coapplicative g) => Coapplicative (Compose f g) where
  copure (Compose a) = copure . fmap copure $ a

instance Coapplicative f => Choice (Costar f) where
  left' (Costar f) = Costar $ either (Left . f) (Right . copure) . branch

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
-- 'Re' 
---------------------------------------------------------------------

-- | Reverse an optic to obtain its dual.
--
-- >>> 5 ^. re left'
-- Left 5
--
-- >>> 6 ^. re (left' . from succ)
-- Left 7
--
-- @
-- 're' . 're'  ≡ id
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


{-
#if !(MIN_VERSION_profunctors(5,5,0))
instance Cochoice (Forget r) where 
  unleft (Forget f) = Forget $ f . Left

  unright (Forget f) = Forget $ f . Right
#endif

#if MIN_VERSION_profunctors(5,4,0)
instance Comonad f => Choice (Costar f) where
  left' (Costar f) = Costar . runCostar . A.left . Costar $ f

  right' (Costar f) = Costar . runCostar . A.right . Costar $ f
#endif
-}

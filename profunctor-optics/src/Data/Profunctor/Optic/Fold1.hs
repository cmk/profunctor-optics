{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Fold1 (
    -- * Fold1 & Ixfold1
    Fold1
  , Ixfold1
  , fold1_
  , folding1
  , fold1Vl
  , toFold1
  , afold1
    -- * Optics
  , folded1 
  , folded1_
  , nonunital
  , presemiring
  , summed1
  , multiplied1
    -- * Primitive operators
  , withFold1
  , withIxfold1
    -- * Operators
  , nelists
  , folds1
    -- * Carriers
  , AFold1
  , AIxfold1
    -- * Auxilliary Types
  , Nedl(..)
) where

import Data.Foldable (Foldable)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Monoid hiding (All(..), Any(..))
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Fold
import Data.Profunctor.Optic.Traversal1
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.View (AView, to, from, withPrimView, view, cloneView)
import Data.Semiring (Semiring(..), Prod(..))
import qualified Data.List.NonEmpty as NEL
import qualified Data.Semiring as Rng

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> import Data.Int.Instance ()
-- >>> import Data.List.NonEmpty (NonEmpty(..))
-- >>> import Data.Map.NonEmpty as Map1
-- >>> import Data.Monoid
-- >>> import Data.Semiring hiding (unital,nonunital,presemiring)
-- >>> import qualified Data.List.NonEmpty as NE
-- >>> :load Data.Profunctor.Optic

type Fold1Rep r = Star (Const r)

type AFold1 r s a = Optic' (FoldRep r) s a

type AIxfold1 r i s a = IndexedOptic' (Fold1Rep r) i s a

---------------------------------------------------------------------
-- 'Fold1' & 'Ixfold1'
---------------------------------------------------------------------

-- | Obtain a 'Fold1' directly.
--
-- @ 
-- 'fold1_' ('nelists' o) ≡ o
-- 'fold1_' f ≡ 'to' f . 'fold1Vl' 'traverse1_'
-- 'fold1_' f ≡ 'coercer' . 'lmap' f . 'lift' 'traverse1_'
-- @
--
-- See 'Data.Profunctor.Optic.Property'.
--
-- This can be useful to repn operations from @Data.List.NonEmpty@ and elsewhere into a 'Fold1'.
--
fold1_ :: Foldable1 f => (s -> f a) -> Fold1 s a
fold1_ f = to f . fold1Vl traverse1_
{-# INLINE fold1_ #-}

-- | Obtain a 'Fold1' from a 'Traversable1' functor.
--
-- @
-- 'folding1' f ≡ 'traversed1' . 'to' f
-- 'folding1' f ≡ 'fold1Vl' 'traverse1' . 'to' f
-- @
--
folding1 :: Traversable1 f => (s -> a) -> Fold1 (f s) a
folding1 f = fold1Vl traverse1 . to f
{-# INLINE folding1 #-}

-- | Obtain a 'Fold1' from a Van Laarhoven 'Fold1'.
--
-- See 'Data.Profunctor.Optic.Property'.
--
fold1Vl :: (forall f. Apply f => (a -> f b) -> s -> f t) -> Fold1 s a
fold1Vl f = coercer . repn f . coercer
{-# INLINE fold1Vl #-}

-- | Obtain a 'Fold1' from a 'View' or 'AFold1'.
--
toFold1 :: AView s a -> Fold1 s a
toFold1 = to . view
{-# INLINE toFold1 #-}

-- | TODO: Document
--
-- @
-- afold1 :: ((a -> r) -> s -> r) -> AFold1 r s a
-- @
--
afold1 :: ((a -> r) -> s -> r) -> Optic (Fold1Rep r) s t a b
afold1 f = Star #. (Const #.) #. f .# (getConst #.) .# runStar
{-# INLINE afold1 #-}

---------------------------------------------------------------------
-- Optics 
---------------------------------------------------------------------

-- | Obtain a 'Fold1' from a 'Traversable1' functor.
--
folded1 :: Traversable1 f => Fold1 (f a) a
folded1 = folding1 id
{-# INLINE folded1 #-}

-- | The canonical 'Fold1'.
--
-- @
-- 'Data.Semigroup.Foldable.foldMap1' ≡ 'withFold1' 'folded1_''
-- @
--
folded1_ :: Foldable1 f => Fold1 (f a) a
folded1_ = fold1_ id
{-# INLINE folded1_ #-}

-- | Expression in a semiring expression with no multiplicative unit.
--
-- @ 
-- 'nonunital' ≡ 'summed' . 'multiplied1'
-- @
--
-- >>> folds1 nonunital $ (fmap . fmap) Just [1 :| [2], 3 :| [4 :: Int]]
-- Just 14
--
nonunital :: Foldable f => Foldable1 g => Monoid r => Semiring r => AFold r (f (g a)) a
nonunital = summed . multiplied1
{-# INLINE nonunital #-}

-- | Expression in a semiring with no additive or multiplicative unit.
--
-- @ 
-- 'presemiring' ≡ 'summed1' . 'multiplied1'
-- @
--
presemiring :: Foldable1 f => Foldable1 g => Semiring r => AFold1 r (f (g a)) a
presemiring = summed1 . multiplied1
{-# INLINE presemiring #-}

-- | Semigroup sum of a non-empty foldable collection.
--
-- >>> 1 <> 2 <> 3 <> 4 :: Int
-- 10
-- >>> folds1 summed1 $ 1 :| [2,3,4 :: Int]
-- 10
--
summed1 :: Foldable1 f => Semigroup r => AFold1 r (f a) a
summed1 = afold foldMap1
{-# INLINE summed1 #-}

-- | Semiring product of a non-empty foldable collection. 
--
-- >>> folds1 multiplied1 $ fmap Just (1 :| [2..(5 :: Int)])
-- Just 120 
--
multiplied1 :: Foldable1 f => Semiring r => AFold1 r (f a) a
multiplied1 = afold Rng.product1
{-# INLINE multiplied1 #-}

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | Map an optic to a semigroup and combine the results.
--
-- @
-- 'withFold1' :: 'Semigroup' r => 'AFold1' r s a -> (a -> r) -> s -> r
-- @
--
withFold1 :: Semigroup r => Optic (Fold1Rep r) s t a b -> (a -> r) -> s -> r
withFold1 = withPrimView
{-# INLINE withFold1 #-}

-- | TODO: Document
--
-- >>> :t flip withIxfold1 Map.singleton
-- flip withIxfold1 Map.singleton
--   :: AIxfold (Map i a) i s a -> i -> s -> Map i a
-- 
-- >>> withIxfold1 itraversed1 const 0 (1 :| [2..5])
-- 10
-- >>> withIxfold1 itraversed1 const 0 (1 :| [])
-- 1
--
withIxfold1 :: Semigroup r => AIxfold1 r i s a -> (i -> a -> r) -> i -> s -> r
withIxfold1 o f = curry $ withFold1 o (uncurry f)
{-# INLINE withIxfold1 #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Extract a 'NonEmpty' of the foci of an optic.
--
-- >>> nelists bitraversed1 ('h' :| "ello", 'w' :| "orld")
-- ('h' :| "ello") :| ['w' :| "orld"]
--
nelists :: AFold1 (Nedl a) s a -> s -> NonEmpty a
nelists l = flip getNedl [] . withFold1 l (Nedl #. (:|))
{-# INLINE nelists #-}

-- | TODO: Document
--
folds1 :: Semigroup a => AFold1 a s a -> s -> a
folds1 = flip withFold1 id
{-# INLINE folds1 #-}

-- | Compute the semiring product of the foci of an optic.
--
folds1p :: Semiring r => AFold (Prod r) s a -> (a -> r) -> s -> r
folds1p o p = getProd . withFold1 o (Prod . p)
{-# INLINE folds1p #-}

--------------------------------------------------------------------
-- Auxilliary Types
--------------------------------------------------------------------

-- A non-empty difference list.
newtype Nedl a = Nedl { getNedl :: [a] -> NEL.NonEmpty a }

instance Semigroup (Nedl a) where
  Nedl f <> Nedl g = Nedl (f . NEL.toList . g)

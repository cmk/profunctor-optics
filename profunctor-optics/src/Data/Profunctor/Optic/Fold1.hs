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
  , fold1_
  , folding1
  , fold1Vl
  , toFold1
  , cloneFold1
    -- * Cofold1 & Cxfold
  , Cofold1
  , cofold1Vl 
  , cofolding1
    -- * Optics
  , folded1 
  , cofolded1 
  , folded1_
  , nonunital
  , presemiring
  , summed1
  , multiplied1
    -- * Primitive operators
  , withFold1 
  , withCofold1
    -- * Operators
  , folds1
  , cofolds1
  , folds1p
  , nelists
    -- * Carriers
  , FoldRep
  , AFold1
  , Cofold1Rep
  , ACofold1
  , afold1
  , acofold1
  , Star(..)
  , Costar(..)
    -- * Classes
  , Representable(..)
  , Corepresentable(..)
  , Contravariant(..)
  , Bifunctor(..)
    -- * Auxilliary Types
  , Nedl(..)
) where

import Control.Applicative
import Control.Monad ((<=<), void)
import Control.Monad.Reader as Reader hiding (lift)
import Control.Monad.State as State hiding (lift)
import Data.Foldable (Foldable, foldMap, traverse_)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe
import Data.Monoid hiding (All(..), Any(..))
import Data.Prd (Prd(..), Min(..), Max(..))
import Data.Prd.Lattice (Lattice(..))
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Fold
import Data.Profunctor.Optic.Prism (right, just, async)
import Data.Profunctor.Optic.Traversal1
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.View (AView, to, from, withPrimView, view, cloneView)
import Data.Semiring (Semiring(..), Prod(..))
import qualified Control.Exception as Ex
import qualified Data.List.NonEmpty as NEL
import qualified Data.Prd as Prd
import qualified Data.Semiring as Rng

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> import Control.Exception hiding (catches)
-- >>> import Data.Functor.Identity
-- >>> import Data.List.Index
-- >>> import Data.List.NonEmpty (NonEmpty(..))
-- >>> import Data.Map as Map
-- >>> import Data.Maybe
-- >>> import Data.Monoid
-- >>> import Data.Semiring hiding (unital,nonunital,presemiring)
-- >>> import Data.Sequence as Seq
-- >>> import qualified Data.List.NonEmpty as NE
-- >>> :load Data.Profunctor.Optic
-- >>> let ixtraversed :: Ixtraversal Int [a] [b] a b ; ixtraversed = ixtraversalVl itraverse

---------------------------------------------------------------------
-- 'Fold1' & 'Ixfold1'
---------------------------------------------------------------------

type AFold1 r s a = Optic' (FoldRep r) s a

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
afold1 :: Semigroup r => ((a -> r) -> s -> r) -> AFold1 r s a
afold1 o = Star #. (Const #.) #. o .# (getConst #.) .# runStar
{-# INLINE afold1 #-}

-- | Obtain a 'Fold1' from a 'AFold1'.
--
cloneFold1 :: Semigroup a => AFold1 a s a -> View s a
cloneFold1 = cloneView
{-# INLINE cloneFold1 #-}

---------------------------------------------------------------------
-- 'Cofold1' & 'Cxfold'
---------------------------------------------------------------------

type Cofold1Rep r = Costar (Const r)

type ACofold1 r t b = Optic' (Cofold1Rep r) t b

-- | Obtain an 'Cofold1' from a 'Distributive' functor. 
--
-- @
-- 'cofolding1' f ≡ 'cotraversed1' . 'from' f
-- 'cofolding1' f ≡ 'cofold1Vl' 'cotraverse' . 'from' f
-- @
--
cofolding1 :: Distributive f => (b -> t) -> Cofold1 (f t) b
cofolding1 f = cofold1Vl cotraverse . from f
{-# INLINE cofolding1 #-}

-- | Obtain a 'Cofold1' from a Van Laarhoven 'Cofold1'.
--
cofold1Vl :: (forall f. Apply f => (f a -> b) -> f s -> t) -> Cofold1 t b
cofold1Vl f = coercel . corepn f . coercel
{-# INLINE cofold1Vl #-}

-- | TODO: Document
--
acofold1 :: ((r -> b) -> r -> t) -> ACofold1 r t b
acofold1 o = Costar #. (.# getConst) #. o .#  (.# Const) .# runCostar  
{-# INLINE acofold1 #-}

---------------------------------------------------------------------
-- Optics 
---------------------------------------------------------------------

-- | Obtain a 'Fold1' from a 'Traversable1' functor.
--
folded1 :: Traversable1 f => Fold1 (f a) a
folded1 = folding1 id
{-# INLINE folded1 #-}

-- | Obtain an 'Cofold1' from a 'Distributive' functor. 
--
cofolded1 :: Distributive f => Cofold1 (f b) b
cofolded1 = cofolding1 id
{-# INLINE cofolded1 #-}

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
-- >>> foldOf nonunital $ (fmap . fmap) Just [1 :| [2], 3 :| [4 :: Int]]
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
-- >>> fold1Of summed1 $ 1 :| [2,3,4 :: Int]
-- 10
--
summed1 :: Foldable1 f => Semigroup r => AFold1 r (f a) a
summed1 = afold1 foldMap1
{-# INLINE summed1 #-}

-- | Semiring product of a non-empty foldable collection. 
--
-- >>> fold1Of multiplied1 $ fmap Just (1 :| [2..(5 :: Int)])
-- Just 120 
--
multiplied1 :: Foldable1 f => Semiring r => AFold1 r (f a) a
multiplied1 = afold1 Rng.product1
{-# INLINE multiplied1 #-}

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | Map an optic to a semigroup and combine the results.
--
withFold1 :: Semigroup r => AFold1 r s a -> (a -> r) -> s -> r
withFold1 = withPrimView
{-# INLINE withFold1 #-}

-- | TODO: Document
--
-- >>> withCofold1 (from succ) (*2) 3
-- 7
--
-- Compare 'Data.Profunctor.Optic.View.withPrimReview'.
--
withCofold1 :: ACofold1 r t b -> (r -> b) -> r -> t
withCofold1 o = (.# Const) #. runCostar #. o .# Costar .# (.# getConst)
{-# INLINE withCofold1 #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | TODO: Document
--
folds1 :: Semigroup a => AFold1 a s a -> s -> a
folds1 = flip withFold1 id
{-# INLINE folds1 #-}

-- | TODO: Document
--
cofolds1 :: ACofold1 b t b -> b -> t
cofolds1 = flip withCofold1 id
{-# INLINE cofolds1 #-}

-- | Compute the semiring product of the foci of an optic.
--
-- For semirings without a multiplicative unit this is equivalent to @const mempty@:
--
-- >>> productOf folded Just [1..(5 :: Int)]
-- Just 0
--
-- In this situation you most likely want to use 'folds1p'.
--
folds1p :: Semiring r => AFold (Prod r) s a -> (a -> r) -> s -> r
folds1p o p = getProd . withFold1 o (Prod . p)
{-# INLINE folds1p #-}

{-
>>> nelists bitraversed1 ('h' :| "ello", 'w' :| "orld")
 "hello" :| ["world"]
-}

-- | Extract a 'NonEmpty' of the foci of an optic.
--
--
-- @
-- 'nelists' :: 'View' s a        -> s -> NonEmpty a
-- 'nelists' :: 'Fold1' s a       -> s -> NonEmpty a
-- 'nelists' :: 'Lens'' s a       -> s -> NonEmpty a
-- 'nelists' :: 'Iso'' s a        -> s -> NonEmpty a
-- 'nelists' :: 'Traversal1'' s a -> s -> NonEmpty a
-- 'nelists' :: 'Prism'' s a      -> s -> NonEmpty a
-- @
--
nelists :: AFold1 (Nedl a) s a -> s -> NonEmpty a
nelists l = flip getNedl [] . withFold1 l (Nedl #. (:|))
{-# INLINE nelists #-}

------------------------------------------------------------------------------
-- Indexed operators
------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- Auxilliary Types
------------------------------------------------------------------------------

-- A non-empty difference list.
newtype Nedl a = Nedl { getNedl :: [a] -> NEL.NonEmpty a }

instance Semigroup (Nedl a) where
  Nedl f <> Nedl g = Nedl (f . NEL.toList . g)

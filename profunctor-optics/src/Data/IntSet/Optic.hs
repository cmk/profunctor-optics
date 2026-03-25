{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
-- | Left and right carriers are characterized by their representation
-- functors ('Rep' and 'Corep'). 'Iso' sits at the top where both
-- are trivial ('Identity'). 'Adjoint' sits at the bottom where they
-- form a full adjunction (@'Corep' p ⊣ 'Rep' p@). A left-indexed
-- ('Ix') optic threads an index through the left adjoint functor
-- @(,) k@, while a right-indexed ('Cx') optic threads a coindex
-- through the right adjoint functor @(->) k@.
--
-- Profunctor optics for 'Data.IntSet.IntSet'.
module Data.IntSet.Optic (
    -- * Types
    IS.IntSet
    -- * Membership
  , member
    -- * Fold
  , folded
    -- * Dual Optics
  , zipped
    -- * Conversion
  , listed
) where

import Data.Profunctor.Optic hiding (zipped, folded)
import Data.Profunctor.Optic.Import
import qualified Data.IntSet as IS
import Prelude

-- | /O(log n)/. 'Fold0' testing membership.
--
member :: Int -> Fold0 IS.IntSet Int
member a = filtered (IS.member a) . to (const a)
{-# INLINE member #-}

-- | /O(n)/. 'Fold' over all elements in ascending order.
--
folded :: Fold IS.IntSet Int
folded = fold_ IS.toAscList
{-# INLINE folded #-}

-- | Grate viewing an IntSet as a predicate (function to Bool).
--
zipped :: IS.IntSet -> Colens IS.IntSet IS.IntSet (Int -> Bool) (Int -> Bool)
zipped universe = grate $ \f -> IS.filter (\a -> f (\s -> flip IS.member s) a) universe
{-# INLINE zipped #-}

-- | 'Iso' between an 'IntSet' and a sorted list.
--
listed :: Iso' IS.IntSet [Int]
listed = iso IS.toAscList IS.fromList
{-# INLINE listed #-}

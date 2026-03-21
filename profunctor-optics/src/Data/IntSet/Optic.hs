{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
-- | Profunctor optics for 'Data.IntSet.IntSet'.
module Data.IntSet.Optic (
    -- * Membership
    member
    -- * Fold
  , folded
    -- * Conversion
  , listed
) where

import Data.Profunctor.Optic hiding (folded)
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

-- | 'Iso' between an 'IntSet' and a sorted list.
--
listed :: Iso' IS.IntSet [Int]
listed = iso IS.toAscList IS.fromList
{-# INLINE listed #-}

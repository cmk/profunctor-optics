{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
-- | Profunctor optics for 'Data.Set.Set'.
module Data.Set.Optic (
    -- * Membership
    member
    -- * Fold
  , folded
    -- * Conversion
  , listed
) where

import Data.Profunctor.Optic hiding (folded)
import Data.Profunctor.Optic.Import
import qualified Data.Set as Set
import Prelude

-- | /O(log n)/. 'Fold0' testing membership.
--
member :: Ord a => a -> Fold0 (Set.Set a) a
member a = filtered (Set.member a) . to (const a)
{-# INLINE member #-}

-- | /O(n)/. 'Fold' over all elements in ascending order.
--
folded :: Fold (Set.Set a) a
folded = fold_ Set.toAscList
{-# INLINE folded #-}

-- | 'Iso' between a 'Set' and a sorted list.
--
listed :: Ord a => Iso' (Set.Set a) [a]
listed = iso Set.toAscList Set.fromList
{-# INLINE listed #-}

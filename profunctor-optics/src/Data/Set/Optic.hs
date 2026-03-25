{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
-- | Profunctor optics for 'Data.Set.Set'.
module Data.Set.Optic (
    -- * Types
    Set.Set
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

-- | Grate viewing a Set as a predicate (function to Bool).
-- The key set parameter defines the universe of elements.
--
-- @zipsWith (zipped universe) (||) s1 s2@ is set union.
-- @zipsWith (zipped universe) (&&) s1 s2@ is set intersection.
--
zipped :: Ord a => Set.Set a -> Colens (Set.Set a) (Set.Set a) (a -> Bool) (a -> Bool)
zipped universe = grate $ \f -> Set.filter (\a -> f (\s -> flip Set.member s) a) universe
{-# INLINE zipped #-}

-- | 'Iso' between a 'Set' and a sorted list.
--
listed :: Ord a => Iso' (Set.Set a) [a]
listed = iso Set.toAscList Set.fromList
{-# INLINE listed #-}

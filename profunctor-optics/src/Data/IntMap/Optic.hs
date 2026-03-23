{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
-- | Profunctor optics for 'Data.IntMap.IntMap'.
--
-- Unprimed variants are lazy. Primed (@'@) variants are strict.
module Data.IntMap.Optic (
    -- ** Lens, Ixlens
    alteredF
  , ixalteredF
    -- ** Traversal, Ixtraversal
  , ixtraversed
    -- ** Traversal0, Ixtraversal0
  , at
  , ixat
  , updated
  -- , updateLooked
  -- , lookedLT
  -- , lookedLE
  -- , lookedGE
  -- , lookedGT
    -- ** Fold, Ixfold
  , values
  , ixfolded
    -- ** Fold0, Ixfold0
  , lookedMin
  , lookedMax
  , validated
    -- ** Setter, Ixsetter
  , adjusted
  , ixmapped
  , ixfiltered
  , altered
  , altered'
  , ixaltered
  --, ixaltered'
    -- * Dual Optics
  , cxmapped
    -- * Operators
  , toIntMapOf
  , countingIntMapOf
) where

import Data.Profunctor.Optic
import Data.Profunctor.Optic.Import
import qualified Data.IntMap.Strict as IM
import qualified Data.IntMap.Lazy as IML
import Prelude

-- | /O(log n)/. Lens into Maybe of a value at a key.
--
alteredF :: Int -> Lens' (IM.IntMap a) (Maybe a)
alteredF k = lensVl $ flip IM.alterF k
{-# INLINE alteredF #-}

-- | /O(log n)/. Indexed lens into Maybe of a value at a key.
--
ixalteredF :: Int -> Ixlens' Int (IM.IntMap a) (Maybe a)
ixalteredF k = ixlensVl $ \kab -> IM.alterF (kab k) k
{-# INLINE ixalteredF #-}

-- | /O(n)/. 'Ixtraversal' over values.
--
ixtraversed :: Ixtraversal Int (IM.IntMap a) (IM.IntMap b) a b
ixtraversed = ixtraversalVl IM.traverseWithKey
{-# INLINE ixtraversed #-}

-- | /O(log n)/. Affine traversal into the value at a key.
--
at :: Int -> Traversal0' (IM.IntMap a) a
at k = traversal0' (IM.lookup k) (flip $ IM.insert k)
{-# INLINE at #-}

-- | /O(log n)/. Indexed affine traversal into the value at a key.
--
ixat :: Int -> Ixtraversal0' Int (IM.IntMap a) a
ixat k = ixtraversal0' (\s -> (k,) <$> IM.lookup k s) (flip $ IM.insert k)
{-# INLINE ixat #-}

-- | /O(log n)/. Update a value at a key.
--
updated :: Int -> Ixsetter Int (IM.IntMap a) (IM.IntMap a) a (Maybe a)
updated k = ixsetter $ \kab -> IM.updateWithKey kab k
{-# INLINE updated #-}

-- | /O(n)/. 'Fold' over all values in ascending key order.
--
values :: Fold (IM.IntMap a) a
values = fold_ IM.toAscList . second'
{-# INLINE values #-}

-- | /O(n)/. 'Ixfold' over values.
--
ixfolded :: Ixfold Int (IM.IntMap a) a
ixfolded = ixfoldVl IM.traverseWithKey
{-# INLINE ixfolded #-}

-- | /O(log n)/. 'Ixfold0' into the value at the minimal key.
--
lookedMin :: Ixfold0 Int (IM.IntMap a) a
lookedMin = ixfold0 IM.lookupMin
{-# INLINE lookedMin #-}

-- | /O(log n)/. 'Ixfold0' into the value at the maximal key.
--
lookedMax :: Ixfold0 Int (IM.IntMap a) a
lookedMax = ixfold0 IM.lookupMax
{-# INLINE lookedMax #-}

-- | /O(n)/. Test if the internal structure is valid.
--
validated :: Fold0 (IM.IntMap a) (IM.IntMap a)
validated = filtered (const True)
{-# INLINE validated #-}

-- | /O(log n)/. Adjust a value at a key.
--
adjusted :: Int -> Ixsetter' Int (IM.IntMap a) a
adjusted k = ixsetter $ \kab -> IM.adjustWithKey kab k
{-# INLINE adjusted #-}

-- | /O(n)/. 'Ixsetter' over values.
--
ixmapped :: Ixsetter Int (IM.IntMap a) (IM.IntMap b) a b
ixmapped = ixsetter IM.mapWithKey
{-# INLINE ixmapped #-}

-- | /O(n)/. 'Ixsetter' filtering values.
--
ixfiltered :: Ixsetter Int (IM.IntMap a) (IM.IntMap a) a Bool
ixfiltered = ixsetter IM.filterWithKey
{-# INLINE ixfiltered #-}

-- | /O(log n)/. Alter (lazy).
--
altered :: Int -> Setter' (IM.IntMap a) (Maybe a)
altered k = setter $ \ab -> IML.alter ab k
{-# INLINE altered #-}

-- | /O(log n)/. Alter (strict, values forced on insert).
--
altered' :: Int -> Setter' (IM.IntMap a) (Maybe a)
altered' k = setter $ \ab -> IM.alter ab k
{-# INLINE altered' #-}

-- | /O(log n)/. Indexed alter.
--
ixaltered :: Int -> Ixsetter' Int (IM.IntMap a) (Maybe a)
ixaltered k = ixsetter $ \kab -> IM.alter (kab k) k
{-# INLINE ixaltered #-}

---------------------------------------------------------------------
-- Coindexed optics
---------------------------------------------------------------------

-- | /O(n)/. Coindexed review for 'IM.IntMap': reconstruct with
-- key-dependent logic. Dual of 'ixmapped'.
--
-- @
-- 'cofoldsWithKey' (cxmapped '#' cxmapped) f r nestedIntMap
-- @
--
cxmapped :: Cxview Int (IM.IntMap a -> IM.IntMap b) (a -> b)
cxmapped = cxfrom IM.mapWithKey
{-# INLINE cxmapped #-}

---------------------------------------------------------------------
-- Sort-based
---------------------------------------------------------------------

-- | Build an 'IM.IntMap' keyed by lens focus from a list.
toIntMapOf :: Lens' s Int -> [s] -> IM.IntMap [s]
toIntMapOf _ [] = IM.empty
toIntMapOf o xs = IM.fromListWith (flip (++)) [(s ^. o, [s]) | s <- xs]
{-# INLINE toIntMapOf #-}

-- | Count occurrences per Int key from a list.
countingIntMapOf :: Lens' s Int -> [s] -> IM.IntMap Int
countingIntMapOf _ [] = IM.empty
countingIntMapOf o xs = IM.fromListWith (+) [(s ^. o, 1 :: Int) | s <- xs]
{-# INLINE countingIntMapOf #-}

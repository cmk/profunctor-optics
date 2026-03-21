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
    -- * Access
    at
  , iat
  , values
    -- * Indexed optics
  , imapped
  , ifiltered
  , itraversed
  , ifolded
    -- * Alter
  , altered
  , altered'
  , ialtered
  , alteredF
  , ialteredF
    -- * Update
  , adjusted
  , updated
    -- * Lookup
  , lookedMin
  , lookedMax
    -- * Validation
  , validated
    -- * Sort-based
  , toIntMapOfL
  , countingIntMapOfL
) where

import Data.Profunctor.Optic
import Data.Profunctor.Optic.Import
import qualified Data.IntMap.Strict as IM
import qualified Data.IntMap.Lazy as IML
import Prelude

-- | /O(log n)/. Affine traversal into the value at a key.
--
at :: Int -> Traversal0' (IM.IntMap a) a
at k = traversal0' (IM.lookup k) (flip $ IM.insert k)
{-# INLINE at #-}

-- | /O(log n)/. Indexed affine traversal into the value at a key.
--
iat :: Int -> Ixtraversal0' Int (IM.IntMap a) a
iat k = ixtraversal0' (\s -> (k,) <$> IM.lookup k s) (flip $ IM.insert k)
{-# INLINE iat #-}

-- | /O(n)/. 'Fold' over all values in ascending key order.
--
values :: Fold (IM.IntMap a) a
values = fold_ IM.toAscList . second'
{-# INLINE values #-}

-- | /O(n)/. 'Ixsetter' over values.
--
imapped :: Ixsetter Int (IM.IntMap a) (IM.IntMap b) a b
imapped = ixsetter IM.mapWithKey
{-# INLINE imapped #-}

-- | /O(n)/. 'Ixsetter' filtering values.
--
ifiltered :: Ixsetter Int (IM.IntMap a) (IM.IntMap a) a Bool
ifiltered = ixsetter IM.filterWithKey
{-# INLINE ifiltered #-}

-- | /O(n)/. 'Ixtraversal' over values.
--
itraversed :: Ixtraversal Int (IM.IntMap a) (IM.IntMap b) a b
itraversed = ixtraversalVl IM.traverseWithKey
{-# INLINE itraversed #-}

-- | /O(n)/. 'Ixfold' over values.
--
ifolded :: Ixfold Int (IM.IntMap a) a
ifolded = ixfoldVl IM.traverseWithKey
{-# INLINE ifolded #-}

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
ialtered :: Int -> Ixsetter' Int (IM.IntMap a) (Maybe a)
ialtered k = ixsetter $ \kab -> IM.alter (kab k) k
{-# INLINE ialtered #-}

-- | /O(log n)/. Lens into Maybe of a value at a key.
--
alteredF :: Int -> Lens' (IM.IntMap a) (Maybe a)
alteredF k = lensVl $ flip IM.alterF k
{-# INLINE alteredF #-}

-- | /O(log n)/. Indexed lens into Maybe of a value at a key.
--
ialteredF :: Int -> Ixlens' Int (IM.IntMap a) (Maybe a)
ialteredF k = ixlensVl $ \kab -> IM.alterF (kab k) k
{-# INLINE ialteredF #-}

-- | /O(log n)/. Adjust a value at a key.
--
adjusted :: Int -> Ixsetter' Int (IM.IntMap a) a
adjusted k = ixsetter $ \kab -> IM.adjustWithKey kab k
{-# INLINE adjusted #-}

-- | /O(log n)/. Update a value at a key.
--
updated :: Int -> Ixsetter Int (IM.IntMap a) (IM.IntMap a) a (Maybe a)
updated k = ixsetter $ \kab -> IM.updateWithKey kab k
{-# INLINE updated #-}

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

---------------------------------------------------------------------
-- Sort-based
---------------------------------------------------------------------

-- | Build an 'IM.IntMap' keyed by lens focus from a list.
toIntMapOfL :: Lens' s Int -> [s] -> IM.IntMap [s]
toIntMapOfL _ [] = IM.empty
toIntMapOfL o xs = IM.fromListWith (flip (++)) [(s ^. o, [s]) | s <- xs]

-- | Count occurrences per Int key from a list.
countingIntMapOfL :: Lens' s Int -> [s] -> IM.IntMap Int
countingIntMapOfL _ [] = IM.empty
countingIntMapOfL o xs = IM.fromListWith (+) [(s ^. o, 1 :: Int) | s <- xs]

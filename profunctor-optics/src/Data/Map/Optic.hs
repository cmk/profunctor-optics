{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
-- | Profunctor optics for 'Data.Map.Map'.
--
-- For structural optics (depth, sizes, rebalanced) that require
-- pattern functors, see @Data.Map.Fold.Optic@ in
-- @profunctor-optics-containers@.
module Data.Map.Optic (
    fromIxfold
  , at
  , iat
  , values
  , imapped
  , ifiltered
  , itraversed
  , ifolded
  , altered
  , ialtered
  , alteredF
  , ialteredF
  , adjusted
  , updated
  , updateLooked
  , lookedMin
  , lookedMax
  , lookedLT
  , lookedLE
  , lookedGE
  , lookedGT
  , validated
) where

import Data.Profunctor.Optic
import Data.Profunctor.Optic.Import
import qualified Data.Map.Lazy as Map
import Prelude

-- | /O(1)/. Create a 'Map.Map' from an 'Ixfold'.
--
fromIxfold :: Ord k => Monoid k => AIxfold (Map.Map k a) k s a -> s -> Map.Map k a
fromIxfold o = foldsWithKey o Map.singleton
{-# INLINE fromIxfold #-}

-- | /O(log n)/. Affine traversal into the value at a key of a 'Map.Map'.
--
at :: Ord k => k -> Traversal0' (Map.Map k a) a
at k = traversal0' (Map.lookup k) (flip $ Map.insert k)
{-# INLINE at #-}

-- | /O(log n)/. Indexed affine traversal into the value at a key of a 'Map.Map'.
--
iat :: Ord k => k -> Ixtraversal0' k (Map.Map k a) a
iat k = ixtraversal0' (\s -> (k,) <$> Map.lookup k s) (flip $ Map.insert k)
{-# INLINE iat #-}

-- | /O(n)/. 'Fold' over the values of a 'Map.Map', in ascending key order.
--
values :: Fold (Map.Map k a) a
values = fold_ Map.toAscList . second'
{-# INLINE values #-}

-- | /O(n)/. 'Ixsetter' over the values of a 'Map.Map'.
--
imapped :: Ixsetter k (Map.Map k a) (Map.Map k b) a b
imapped = ixsetter Map.mapWithKey
{-# INLINE imapped #-}

-- | /O(n)/. 'Ixsetter' filtering the values of a 'Map.Map'.
--
ifiltered :: Ixsetter k (Map.Map k a) (Map.Map k a) a Bool
ifiltered = ixsetter Map.filterWithKey
{-# INLINE ifiltered #-}

-- | /O(n)/. 'Ixtraversal' over the values of a 'Map.Map'.
--
itraversed :: Ord k => Ixtraversal k (Map.Map k a) (Map.Map k b) a b
itraversed = ixtraversalVl Map.traverseWithKey
{-# INLINE itraversed #-}

-- | /O(n)/. 'Ixfold' over the values of a 'Map.Map'.
--
ifolded :: Ixfold k (Map.Map k a) a
ifolded = ixfoldVl Map.traverseWithKey
{-# INLINE ifolded #-}

-- | /O(log n)/. Alter the value at a specific key.
--
altered :: Ord k => k -> Setter' (Map.Map k a) (Maybe a)
altered k = setter $ \ab -> Map.alter ab k
{-# INLINE altered #-}

-- | /O(log n)/. Indexed alter.
--
ialtered :: Ord k => k -> Ixsetter' k (Map.Map k a) (Maybe a)
ialtered k = ixsetter $ \kab -> Map.alter (kab k) k
{-# INLINE ialtered #-}

-- | /O(log n)/. Lens into /Maybe/ of a value at a key.
--
alteredF :: Ord k => k -> Lens' (Map.Map k a) (Maybe a)
alteredF k = lensVl $ flip Map.alterF k
{-# INLINE alteredF #-}

-- | /O(log n)/. Indexed lens into /Maybe/ of a value at a key.
--
ialteredF :: Ord k => k -> Ixlens' k (Map.Map k a) (Maybe a)
ialteredF k = ixlensVl $ \kab -> Map.alterF (kab k) k
{-# INLINE ialteredF #-}

-- | /O(log n)/. Adjust a value at a specific key.
--
adjusted :: Ord k => k -> Ixsetter' k (Map.Map k a) a
adjusted k = ixsetter $ \kab -> Map.adjustWithKey kab k
{-# INLINE adjusted #-}

-- | /O(log n)/. Update a value at a specific key.
--
updated :: Ord k => k -> Ixsetter k (Map.Map k a) (Map.Map k a) a (Maybe a)
updated k = ixsetter $ \kab -> Map.updateWithKey kab k
{-# INLINE updated #-}

-- | /O(log n)/. Lookup and update a value at a specific key.
--
updateLooked :: Ord k => k -> Ixsetter k (Map.Map k a) (Maybe a, Map.Map k a) a (Maybe a)
updateLooked k = ixsetter $ \kab -> Map.updateLookupWithKey kab k
{-# INLINE updateLooked #-}

-- | /O(log n)/. 'Ixfold0' into the value at the minimal key.
--
lookedMin :: Ixfold0 k (Map.Map k a) a
lookedMin = ixfold0 Map.lookupMin
{-# INLINE lookedMin #-}

-- | /O(log n)/. 'Ixfold0' into the value at the maximal key.
--
lookedMax :: Ixfold0 k (Map.Map k a) a
lookedMax = ixfold0 Map.lookupMax
{-# INLINE lookedMax #-}

-- | /O(log n)/. Indexed affine traversal into the value at the largest key smaller than the given one.
--
lookedLT :: Ord k => k -> Ixtraversal0' k (Map.Map k a) a
lookedLT k = ixtraversal0' (Map.lookupLT k) (flip $ Map.insert k)
{-# INLINE lookedLT #-}

-- | /O(log n)/. Indexed affine traversal into the value at the largest key smaller than or equal to the given one.
--
lookedLE :: Ord k => k -> Ixtraversal0' k (Map.Map k a) a
lookedLE k = ixtraversal0' (Map.lookupLE k) (flip $ Map.insert k)
{-# INLINE lookedLE #-}

-- | /O(log n)/. Indexed affine traversal into the value at the smallest key greater than or equal to the given one.
--
lookedGE :: Ord k => k -> Ixtraversal0' k (Map.Map k a) a
lookedGE k = ixtraversal0' (Map.lookupGE k) (flip $ Map.insert k)
{-# INLINE lookedGE #-}

-- | /O(log n)/. Indexed affine traversal into the value at the smallest key greater than the given one.
--
lookedGT :: Ord k => k -> Ixtraversal0' k (Map.Map k a) a
lookedGT k = ixtraversal0' (Map.lookupGT k) (flip $ Map.insert k)
{-# INLINE lookedGT #-}

-- | /O(n)/. Test if the internal map structure is valid.
--
validated :: Ord k => Fold0 (Map.Map k a) (Map.Map k a)
validated = filtered Map.valid
{-# INLINE validated #-}

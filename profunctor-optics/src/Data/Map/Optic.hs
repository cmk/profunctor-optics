{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
-- | Profunctor optics for 'Data.Map.Map'.
--
-- Unprimed variants are lazy. Primed (@'@) variants are strict.
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
    -- * Strict variants
  , altered'
  , ialtered'
    -- * Sort-based operators
  , toMapOfL
  , countingOfL
  , foldSortingL
  , foldSorting1L
  , mconcatSortingL
    -- * Merge (Sort + containers merge)
  , mergingOfL
  , innerMergeL
  , outerMergeL
  , leftMergeL
  , rightMergeL
    -- * Sort merge tactics
  , sortedMatched
  , sortedMissing
    -- * Coindexed optics
  , cxmapped
) where

import Data.Profunctor.Optic hiding (toMapOfL, countingOfL, sortingOfL, sortingDescOfL, groupingOfL, nubbingOfL, foldSortingL, foldSorting1L, mconcatSortingL, sortingString, mergingOfL, innerMergeL, outerMergeL, leftMergeL, rightMergeL, sortedMatched, sortedMissing)
import Data.Profunctor.Optic.Carrier (Sort(..), runSort)
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.View (cxfrom)
import qualified Data.Map.Lazy as Map
import qualified Data.Map.Strict as MapS
import qualified Data.Map.Merge.Strict as Merge
import Prelude

-- | /O(1)/. Create a 'Map.Map' from an 'Ixfold'.
--
fromIxfold :: Ord k => Monoid k => AIxfold (Map.Map k a) k s a -> s -> Map.Map k a
fromIxfold o = ixfoldMapOf o Map.singleton
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

-- | /O(log n)/. Alter the value at a specific key (lazy).
--
altered :: Ord k => k -> Setter' (Map.Map k a) (Maybe a)
altered k = setter $ \ab -> Map.alter ab k
{-# INLINE altered #-}

-- | /O(log n)/. Indexed alter (lazy).
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

---------------------------------------------------------------------
-- Strict variants
---------------------------------------------------------------------

-- | /O(log n)/. Strict alter (values forced on insert).
--
altered' :: Ord k => k -> Setter' (Map.Map k a) (Maybe a)
altered' k = setter $ \ab -> MapS.alter ab k
{-# INLINE altered' #-}

-- | /O(log n)/. Strict indexed alter.
--
ialtered' :: Ord k => k -> Ixsetter' k (Map.Map k a) (Maybe a)
ialtered' k = ixsetter $ \kab -> MapS.alter (kab k) k
{-# INLINE ialtered' #-}

---------------------------------------------------------------------
-- Sort-based operators
---------------------------------------------------------------------

-- | Build a 'Map.Map' keyed by lens focus from a list.
--
-- /Benchmark: 1.01x vs direct Map.fromListWith (zero-cost). See "Data.Profunctor.Optic.Bench"./
--
toMapOfL :: Ord a => Lens' s a -> [s] -> MapS.Map a [s]
toMapOfL _ [] = MapS.empty
toMapOfL o xs = MapS.fromListWith (flip (++)) [(s ^. o, [s]) | s <- xs]

-- | Count occurrences per key from a list.
countingOfL :: Ord a => Lens' s a -> [s] -> MapS.Map a Int
countingOfL _ [] = MapS.empty
countingOfL o xs = MapS.fromListWith (+) [(s ^. o, 1 :: Int) | s <- xs]

-- | Sort through a lens, then right-fold each group.
foldSortingL :: Ord a => Lens' s a -> (s -> r -> r) -> r -> [s] -> [r]
foldSortingL o g z xs = map (foldr g z) (MapS.elems $ toMapOfL o xs)

-- | Sort through a lens, then reduce each non-empty group.
foldSorting1L :: Ord a => Lens' s a -> (s -> s -> s) -> [s] -> [s]
foldSorting1L o f xs = map (foldr1 f) (MapS.elems $ toMapOfL o xs)

-- | Sort through a lens, then monoidal concat per group.
mconcatSortingL :: (Ord a, Monoid m) => Lens' s a -> (s -> m) -> [s] -> [m]
mconcatSortingL o g xs = map (foldMap g) (MapS.elems $ toMapOfL o xs)

---------------------------------------------------------------------
-- Merge (Sort + containers merge)
---------------------------------------------------------------------

-- | Merge two toListOf through lenses using containers merge tactics.
mergingOfL :: Ord a
           => Lens' s a -> Lens' t a
           -> Merge.SimpleWhenMissing a [s] c
           -> Merge.SimpleWhenMissing a [t] c
           -> Merge.SimpleWhenMatched a [s] [t] c
           -> [s] -> [t] -> Map.Map a c
mergingOfL lo ro wml wmr wm xs ys =
  Merge.merge wml wmr wm (toMapOfL lo xs) (toMapOfL ro ys)

-- | Inner merge: only keys present in both inputs.
innerMergeL :: Ord a
            => Lens' s a -> Lens' t a
            -> (a -> [s] -> [t] -> c)
            -> [s] -> [t] -> Map.Map a c
innerMergeL lo ro f =
  mergingOfL lo ro Merge.dropMissing Merge.dropMissing (Merge.zipWithMatched f)

-- | Full outer merge.
outerMergeL :: Ord a
            => Lens' s a -> Lens' t a
            -> (a -> [s] -> c) -> (a -> [t] -> c) -> (a -> [s] -> [t] -> c)
            -> [s] -> [t] -> Map.Map a c
outerMergeL lo ro fl fr fb =
  mergingOfL lo ro (Merge.mapMissing fl) (Merge.mapMissing fr) (Merge.zipWithMatched fb)

-- | Left merge: all keys from left.
leftMergeL :: Ord a
           => Lens' s a -> Lens' t a
           -> (a -> [s] -> c) -> (a -> [s] -> [t] -> c)
           -> [s] -> [t] -> Map.Map a c
leftMergeL lo ro fl fb =
  mergingOfL lo ro (Merge.mapMissing fl) Merge.dropMissing (Merge.zipWithMatched fb)

-- | Right merge: all keys from right.
rightMergeL :: Ord a
            => Lens' s a -> Lens' t a
            -> (a -> [t] -> c) -> (a -> [s] -> [t] -> c)
            -> [s] -> [t] -> Map.Map a c
rightMergeL lo ro fr fb =
  mergingOfL lo ro Merge.dropMissing (Merge.mapMissing fr) (Merge.zipWithMatched fb)

---------------------------------------------------------------------
-- Sort merge tactics
---------------------------------------------------------------------

-- | Construct a 'WhenMatched' merge tactic from a 'Sort'.
-- Uses @i = ()@ (one position per key).
sortedMatched :: Sort () k (x, y) z -> Merge.SimpleWhenMatched k x y z
sortedMatched (Sort h) = Merge.zipWithMatched $ \k x y ->
  h (const (k, (x, y)))

-- | Construct a 'WhenMissing' merge tactic from a 'Sort'.
-- Uses @i = ()@ (one position per key).
sortedMissing :: Sort () k x y -> Merge.SimpleWhenMissing k x y
sortedMissing (Sort h) = Merge.mapMissing $ \k x ->
  h (const (k, x))

---------------------------------------------------------------------
-- Coindexed optics
---------------------------------------------------------------------

-- | /O(n)/. Coindexed review for 'Map.Map': reconstruct a map
-- with key-dependent logic.
--
-- Built via 'cxfrom' 'Data.Map.mapWithKey'. The coindex @k@ is the
-- map key — available on the reconstruction side. Dual of 'imapped'.
--
-- Compose with '(#)' for multi-level coindexed operations:
--
-- @
-- 'cxfoldMapOf' (cxmapped '#' cxmapped) f r nestedMap
-- @
--
cxmapped :: Cxreview k (MapS.Map k a -> MapS.Map k b) (a -> b)
cxmapped = cxfrom Map.mapWithKey
{-# INLINE cxmapped #-}


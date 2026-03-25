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
    -- * Types
    IM.IntMap
    -- * Optics
    -- ** Lens, Ixlens
  , alteredF
  , ixalteredF
    -- ** Traversal, Ixtraversal
  , ixtraversed
    -- ** Traversal0, Ixtraversal0
  , at
  , ixat
  , updated
  , updateLooked
  , lookedLT
  , lookedLE
  , lookedGE
  , lookedGT
    -- ** Fold, Ixfold
  , values
  , ixfolded
    -- ** Fold0, Ixfold0
  , lookedMin
  , lookedMax
    -- ** Setter, Ixsetter
  , mapped
  , adjusted
  , ixmapped
  , ixfiltered
  , altered
  , altered'
  , ixaltered
  , ixaltered'
    -- * Dual Optics
    -- ** Colens
  , zipsIntMap
    -- ** Cotraversal
  , zippedIntMap
    -- ** Cxtraversal
  , cxtraversed
  , cxzippedIntMap
    -- ** Cosetter
  , comapped
    -- ** Cxsetter
  , cxmapped
  , cxfiltered
  , cxmappedIf
    -- ** Cxfold
  , cxfolded
    -- ** Cxview
  , cxmapped'
    -- * Operators
  , toIntMapOf
  , countsOf
    -- ** Sort-based
  , foldSorts
  , foldSorts1
  , mconcatSorts
    -- ** Merge (Sort + containers merge)
  , merges
  , innerMerges
  , outerMerges
  , leftMerges
  , rightMerges
    -- ** Sort merge tactics
  , sortingMatched
  , sortingMissing
) where

import Data.Profunctor.Optic hiding (toMapOf, countsOf, foldSorts, foldSorts1, mconcatSorts, sortingString, merges, innerMerges, outerMerges, leftMerges, rightMerges, sortedMatched, sortedMissing)
import Data.Profunctor.Optic.Import
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.IntMap.Strict as IM
import qualified Data.IntMap.Lazy as IML
import qualified Data.IntMap.Merge.Strict as Merge
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

-- | /O(log n)/. Lookup and update a value at a specific key.
--
updateLooked :: Int -> Ixsetter Int (IM.IntMap a) (Maybe a, IM.IntMap a) a (Maybe a)
updateLooked k = ixsetter $ \kab -> IM.updateLookupWithKey kab k
{-# INLINE updateLooked #-}

-- | /O(log n)/. Indexed affine traversal into the value at the largest key smaller than the given one.
--
lookedLT :: Int -> Ixtraversal0' Int (IM.IntMap a) a
lookedLT k = ixtraversal0' (IM.lookupLT k) (flip $ IM.insert k)
{-# INLINE lookedLT #-}

-- | /O(log n)/. Indexed affine traversal into the value at the largest key smaller than or equal to the given one.
--
lookedLE :: Int -> Ixtraversal0' Int (IM.IntMap a) a
lookedLE k = ixtraversal0' (IM.lookupLE k) (flip $ IM.insert k)
{-# INLINE lookedLE #-}

-- | /O(log n)/. Indexed affine traversal into the value at the smallest key greater than or equal to the given one.
--
lookedGE :: Int -> Ixtraversal0' Int (IM.IntMap a) a
lookedGE k = ixtraversal0' (IM.lookupGE k) (flip $ IM.insert k)
{-# INLINE lookedGE #-}

-- | /O(log n)/. Indexed affine traversal into the value at the smallest key greater than the given one.
--
lookedGT :: Int -> Ixtraversal0' Int (IM.IntMap a) a
lookedGT k = ixtraversal0' (IM.lookupGT k) (flip $ IM.insert k)
{-# INLINE lookedGT #-}

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

-- | /O(n)/. Non-indexed 'Setter' over the values of an 'IM.IntMap'.
--
-- @'over' 'mapped' f = 'fmap' f@
--
mapped :: Setter (IM.IntMap a) (IM.IntMap b) a b
mapped = setter fmap
{-# INLINE mapped #-}

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

-- | /O(log n)/. Indexed alter (lazy).
--
ixaltered :: Int -> Ixsetter' Int (IM.IntMap a) (Maybe a)
ixaltered k = ixsetter $ \kab -> IML.alter (kab k) k
{-# INLINE ixaltered #-}

-- | /O(log n)/. Indexed alter (strict, values forced on insert).
--
ixaltered' :: Int -> Ixsetter' Int (IM.IntMap a) (Maybe a)
ixaltered' k = ixsetter $ \kab -> IM.alter (kab k) k
{-# INLINE ixaltered' #-}

---------------------------------------------------------------------
-- Dual optics
---------------------------------------------------------------------

-- | Grate viewing an IntMap as a function from Int keys.
-- Requires a fixed key set to be representable.
--
zipsIntMap :: IntSet -> Colens (IM.IntMap a) (IM.IntMap b) (Int -> a) (Int -> b)
zipsIntMap ks = grate $ \f -> IM.fromList [(k, f (\m k' -> IM.findWithDefault (error "zipsIntMap: missing key") k' m) k) | k <- IntSet.toList ks]
{-# INLINE zipsIntMap #-}

-- | Pointwise 'Cotraversal' over the values of an 'IM.IntMap' at a
-- fixed key set. Extends 'zipsIntMap' from 'Colens' to 'Cotraversal':
-- where 'zipsIntMap' views the map as a function from keys,
-- 'zippedIntMap' views it as a container that can be zipped pointwise.
--
-- Requires a fixed key set because 'IM.IntMap' is not 'Distributive'
-- (it has variable size).
--
zippedIntMap :: IntSet -> Cotraversal (IM.IntMap a) (IM.IntMap b) a b
zippedIntMap ks = cotraversalVl $ \fab fs ->
  IM.fromSet (\k -> fab (fmap (IM.! k) fs)) ks
{-# INLINE zippedIntMap #-}

-- | /O(n)/. Non-indexed 'Cosetter' over the values of an 'IM.IntMap'.
--
-- @'cosets' 'comapped' f = 'fmap' f@
--
comapped :: Cosetter (IM.IntMap a) (IM.IntMap b) a b
comapped = cosetter fmap
{-# INLINE comapped #-}

-- | Keyed pointwise 'Cxtraversal' over the values of an 'IM.IntMap'.
-- Threads the key as coindex. Combines 'zippedIntMap' with
-- key-dependent operations.
--
cxzippedIntMap :: IntSet -> Cxtraversal Int (IM.IntMap a) (IM.IntMap b) a b
cxzippedIntMap ks = cxtraversalVl $ \fakb fs ->
  IM.fromSet (\k -> fakb (fmap (IM.! k) fs) k) ks
{-# INLINE cxzippedIntMap #-}

---------------------------------------------------------------------
-- Coindexed optics
---------------------------------------------------------------------

-- | /O(n)/. Coindexed review for 'IM.IntMap': reconstruct with
-- key-dependent logic. Dual of 'ixmapped'.
--
-- @
-- 'cxfoldMapOf' (cxmapped' '#' cxmapped') f r nestedIntMap
-- @
--
cxmapped' :: Cxview Int (IM.IntMap a -> IM.IntMap b) (a -> b)
cxmapped' = cxfrom IM.mapWithKey
{-# INLINE cxmapped' #-}

-- | /O(n)/. 'Cxsetter' over the values of an 'IM.IntMap'.
--
-- Cx dual of 'ixmapped'. Threads the key as coindex on the
-- Costar side, composable with 'Colens' chains.
--
-- @
-- 'cxsets' cxmapped ≡ 'Data.IntMap.mapWithKey'
-- @
--
cxmapped :: Cxsetter Int (IM.IntMap a) (IM.IntMap b) a b
cxmapped = cxsetter IM.mapWithKey
{-# INLINE cxmapped #-}

-- | /O(n)/. 'Cxsetter' filtering the values of an 'IM.IntMap'.
--
-- Cx dual of 'ixfiltered'. Keeps entries where the coindexed
-- predicate returns 'True'.
--
-- @
-- 'cxsets' cxfiltered ≡ 'Data.IntMap.filterWithKey'
-- @
--
cxfiltered :: Cxsetter Int (IM.IntMap a) (IM.IntMap a) a Bool
cxfiltered = cxsetter IM.filterWithKey
{-# INLINE cxfiltered #-}

-- | /O(n)/. 'Cxsetter' that simultaneously maps and filters the
-- values of an 'IM.IntMap'.
--
-- @
-- 'cxsets' cxmappedIf ≡ 'Data.IntMap.mapMaybeWithKey'
-- @
--
cxmappedIf :: Cxsetter Int (IM.IntMap a) (IM.IntMap b) a (Maybe b)
cxmappedIf = cxsetter IM.mapMaybeWithKey
{-# INLINE cxmappedIf #-}

-- | /O(n)/. 'Cxtraversal' over the values of an 'IM.IntMap'.
--
-- Cx dual of 'ixtraversed'. Threads the key as coindex.
--
-- @
-- 'cxtraverseOf' cxtraversed ≡ 'Data.IntMap.traverseWithKey'
-- @
--
cxtraversed :: Cxtraversal Int (IM.IntMap a) (IM.IntMap b) a b
cxtraversed = cxtraversalVl $ \fakb fs ->
  IM.fromSet (\k -> fakb (fmap (IM.! k) fs) k) (IM.keysSet (copure fs))
{-# INLINE cxtraversed #-}

-- | /O(n)/. 'Cxfold' over the values of an 'IM.IntMap'.
--
-- Cx dual of 'ixfolded'. Threads the key as coindex.
--
cxfolded :: Cxfold Int (IM.IntMap a) a
cxfolded = cxfoldVl $ \fakb fs ->
  IM.fromSet (\k -> fakb (fmap (IM.! k) fs) k) (IM.keysSet (copure fs))
{-# INLINE cxfolded #-}

---------------------------------------------------------------------
-- Sort-based
---------------------------------------------------------------------

-- | Build an 'IM.IntMap' keyed by lens focus from a list.
toIntMapOf :: Lens' s Int -> [s] -> IM.IntMap [s]
toIntMapOf _ [] = IM.empty
toIntMapOf o xs = IM.fromListWith (flip (++)) [(s ^. o, [s]) | s <- xs]
{-# INLINE toIntMapOf #-}

-- | Count occurrences per Int key from a list.
countsOf :: Lens' s Int -> [s] -> IM.IntMap Int
countsOf _ [] = IM.empty
countsOf o xs = IM.fromListWith (+) [(s ^. o, 1 :: Int) | s <- xs]
{-# INLINE countsOf #-}

---------------------------------------------------------------------
-- Post-sort fold (IntMap)
---------------------------------------------------------------------

-- | Sort through an Int lens, then right-fold each group.
foldSorts :: Lens' s Int -> (s -> r -> r) -> r -> [s] -> [r]
foldSorts o g z xs = map (foldr g z) (IM.elems $ toIntMapOf o xs)

-- | Sort through an Int lens, then reduce each non-empty group.
foldSorts1 :: Lens' s Int -> (s -> s -> s) -> [s] -> [s]
foldSorts1 o f xs = map (foldr1 f) (IM.elems $ toIntMapOf o xs)

-- | Sort through an Int lens, then monoidal concat per group.
mconcatSorts :: Monoid m => Lens' s Int -> (s -> m) -> [s] -> [m]
mconcatSorts o g xs = map (foldMap g) (IM.elems $ toIntMapOf o xs)

---------------------------------------------------------------------
-- Merge (Sort + containers merge)
---------------------------------------------------------------------

-- | Merge two lists through 'Int' lenses using containers merge tactics.
merges :: Lens' s Int -> Lens' t Int
       -> Merge.SimpleWhenMissing [s] c
       -> Merge.SimpleWhenMissing [t] c
       -> Merge.SimpleWhenMatched [s] [t] c
       -> [s] -> [t] -> IM.IntMap c
merges lo ro wml wmr wm xs ys =
  Merge.merge wml wmr wm (toIntMapOf lo xs) (toIntMapOf ro ys)

-- | Inner merge: only keys present in both inputs.
innerMerges :: Lens' s Int -> Lens' t Int
            -> (Int -> [s] -> [t] -> c)
            -> [s] -> [t] -> IM.IntMap c
innerMerges lo ro f =
  merges lo ro Merge.dropMissing Merge.dropMissing (Merge.zipWithMatched f)

-- | Full outer merge.
outerMerges :: Lens' s Int -> Lens' t Int
            -> (Int -> [s] -> c) -> (Int -> [t] -> c) -> (Int -> [s] -> [t] -> c)
            -> [s] -> [t] -> IM.IntMap c
outerMerges lo ro fl fr fb =
  merges lo ro (Merge.mapMissing fl) (Merge.mapMissing fr) (Merge.zipWithMatched fb)

-- | Left merge: all keys from left.
leftMerges :: Lens' s Int -> Lens' t Int
           -> (Int -> [s] -> c) -> (Int -> [s] -> [t] -> c)
           -> [s] -> [t] -> IM.IntMap c
leftMerges lo ro fl fb =
  merges lo ro (Merge.mapMissing fl) Merge.dropMissing (Merge.zipWithMatched fb)

-- | Right merge: all keys from right.
rightMerges :: Lens' s Int -> Lens' t Int
            -> (Int -> [t] -> c) -> (Int -> [s] -> [t] -> c)
            -> [s] -> [t] -> IM.IntMap c
rightMerges lo ro fr fb =
  merges lo ro Merge.dropMissing (Merge.mapMissing fr) (Merge.zipWithMatched fb)

---------------------------------------------------------------------
-- Sort merge tactics
---------------------------------------------------------------------

-- | Construct a 'WhenMatched' merge tactic from a 'Sort'.
-- Uses @i = ()@ (one position per key).
sortingMatched :: Sort () Int (x, y) z -> Merge.SimpleWhenMatched x y z
sortingMatched (Sort h) = Merge.zipWithMatched $ \k x y ->
  h (const (k, (x, y)))

-- | Construct a 'WhenMissing' merge tactic from a 'Sort'.
-- Uses @i = ()@ (one position per key).
sortingMissing :: Sort () Int x y -> Merge.SimpleWhenMissing x y
sortingMissing (Sort h) = Merge.mapMissing $ \k x ->
  h (const (k, x))

{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
-- | Profunctor optics for 'Data.Map.Map'.
--
-- Unprimed variants are lazy. Primed (@\'@) variants are strict.
--
-- For structural optics (depth, sizes, rebalanced) that require
-- pattern functors, see @Data.Map.Fold.Optic@ in
-- @profunctor-optics-containers@.
module Data.Map.Optic (
    -- * Optics
    -- ** Lens, Ixlens
    alteredF
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
  , validated
    -- ** Setter, Ixsetter
  , adjusted
  , ixmapped
  , ixfiltered
  , altered
  , altered'
  , ixaltered
  , ixaltered'
    -- * Dual Optics
    -- ** Colens
  , zipsMap
    -- ** Cxtraversal
  , cxtraversed
    -- ** Cxfold
  , cxfolded
    -- ** Cxview
  , cxmapped'
    -- ** Cxsetter
  , cxmapped
  , cxfiltered
  , cxmapMaybed
    -- * Operators
  , fromIxfold
    -- ** Sort-based
  , toMapOf
  , countsOf
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
  , sortedMatched
  , sortedMissing
) where

import Data.Profunctor.Optic hiding (toMapOf, countsOf, foldSorts, foldSorts1, mconcatSorts, sortingString, merges, innerMerges, outerMerges, leftMerges, rightMerges, sortedMatched, sortedMissing)
import Data.Profunctor.Optic.Sort (Sort(..))
import Data.Profunctor.Optic.Import
import Data.Set (Set)
import qualified Data.Map.Lazy as Map
import qualified Data.Map.Strict as MapS
import qualified Data.Map.Merge.Strict as Merge
import Prelude

-- | /O(log n)/. Lens into /Maybe/ of a value at a key.
--
alteredF :: Ord k => k -> Lens' (Map.Map k a) (Maybe a)
alteredF k = lensVl $ flip Map.alterF k
{-# INLINE alteredF #-}

-- | /O(log n)/. Indexed lens into /Maybe/ of a value at a key.
--
ixalteredF :: Ord k => k -> Ixlens' k (Map.Map k a) (Maybe a)
ixalteredF k = ixlensVl $ \kab -> Map.alterF (kab k) k
{-# INLINE ixalteredF #-}

-- | /O(n)/. 'Ixtraversal' over the values of a 'Map.Map'.
--
ixtraversed :: Ord k => Ixtraversal k (Map.Map k a) (Map.Map k b) a b
ixtraversed = ixtraversalVl Map.traverseWithKey
{-# INLINE ixtraversed #-}

-- | /O(log n)/. Affine traversal into the value at a key of a 'Map.Map'.
--
at :: Ord k => k -> Traversal0' (Map.Map k a) a
at k = traversal0' (Map.lookup k) (flip $ Map.insert k)
{-# INLINE at #-}

-- | /O(log n)/. Indexed affine traversal into the value at a key of a 'Map.Map'.
--
ixat :: Ord k => k -> Ixtraversal0' k (Map.Map k a) a
ixat k = ixtraversal0' (\s -> (k,) <$> Map.lookup k s) (flip $ Map.insert k)
{-# INLINE ixat #-}

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

-- | /O(n)/. 'Fold' over the values of a 'Map.Map', in ascending key order.
--
values :: Fold (Map.Map k a) a
values = fold_ Map.toAscList . second'
{-# INLINE values #-}

-- | /O(n)/. 'Ixfold' over the values of a 'Map.Map'.
--
ixfolded :: Ixfold k (Map.Map k a) a
ixfolded = ixfoldVl Map.traverseWithKey
{-# INLINE ixfolded #-}

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

-- | /O(n)/. Test if the internal map structure is valid.
--
validated :: Ord k => Fold0 (Map.Map k a) (Map.Map k a)
validated = filtered Map.valid
{-# INLINE validated #-}

-- | /O(log n)/. Adjust a value at a specific key.
--
adjusted :: Ord k => k -> Ixsetter' k (Map.Map k a) a
adjusted k = ixsetter $ \kab -> Map.adjustWithKey kab k
{-# INLINE adjusted #-}

-- | /O(n)/. 'Ixsetter' over the values of a 'Map.Map'.
--
ixmapped :: Ixsetter k (Map.Map k a) (Map.Map k b) a b
ixmapped = ixsetter Map.mapWithKey
{-# INLINE ixmapped #-}

-- | /O(n)/. 'Ixsetter' filtering the values of a 'Map.Map'.
--
ixfiltered :: Ixsetter k (Map.Map k a) (Map.Map k a) a Bool
ixfiltered = ixsetter Map.filterWithKey
{-# INLINE ixfiltered #-}

-- | /O(log n)/. Alter the value at a specific key (lazy).
--
altered :: Ord k => k -> Setter' (Map.Map k a) (Maybe a)
altered k = setter $ \ab -> Map.alter ab k
{-# INLINE altered #-}

-- | /O(log n)/. Strict alter (values forced on insert).
--
altered' :: Ord k => k -> Setter' (Map.Map k a) (Maybe a)
altered' k = setter $ \ab -> MapS.alter ab k
{-# INLINE altered' #-}

-- | /O(log n)/. Indexed alter (lazy).
--
ixaltered :: Ord k => k -> Ixsetter' k (Map.Map k a) (Maybe a)
ixaltered k = ixsetter $ \kab -> Map.alter (kab k) k
{-# INLINE ixaltered #-}

-- | /O(log n)/. Strict indexed alter.
--
ixaltered' :: Ord k => k -> Ixsetter' k (Map.Map k a) (Maybe a)
ixaltered' k = ixsetter $ \kab -> MapS.alter (kab k) k
{-# INLINE ixaltered' #-}

---------------------------------------------------------------------
-- Dual optics
---------------------------------------------------------------------

-- | Grate viewing a Map as a function from keys.
-- Requires a fixed key set to be representable.
--
zipsMap :: Ord k => Set k -> Colens (Map.Map k a) (Map.Map k b) (k -> a) (k -> b)
zipsMap ks = grate $ \f -> Map.fromSet (\k -> f (\m k' -> Map.findWithDefault (error "zipsMap: missing key") k' m) k) ks
{-# INLINE zipsMap #-}

---------------------------------------------------------------------
-- Coindexed optics
---------------------------------------------------------------------

-- | /O(n)/. Coindexed review for 'Map.Map': reconstruct a map
-- with key-dependent logic.
--
-- Built via 'cxfrom' 'Data.Map.mapWithKey'. The coindex @k@ is the
-- map key — available on the reconstruction side. Dual of 'ixmapped'.
--
-- Compose with '(#)' for multi-level coindexed operations:
--
-- @
-- 'cxfoldMapOf' (cxmapped '#' cxmapped) f r nestedMap
-- @
--
cxmapped' :: Cxview k (MapS.Map k a -> MapS.Map k b) (a -> b)
cxmapped' = cxfrom Map.mapWithKey
{-# INLINE cxmapped' #-}

-- | /O(n)/. 'Cxsetter' over the values of a 'Map.Map'.
--
-- Cx dual of 'ixmapped'. Threads the key as coindex on the
-- Costar side, composable with 'Colens' chains.
--
-- @
-- 'cxsets' cxmapped ≡ 'Data.Map.mapWithKey'
-- @
--
cxmapped :: Cxsetter k (Map.Map k a) (Map.Map k b) a b
cxmapped = cxsetter Map.mapWithKey
{-# INLINE cxmapped #-}

-- | /O(n)/. 'Cxsetter' filtering the values of a 'Map.Map'.
--
-- Cx dual of 'ixfiltered'. Keeps entries where the coindexed
-- predicate returns 'True'.
--
-- @
-- 'cxsets' cxfiltered ≡ 'Data.Map.filterWithKey'
-- @
--
cxfiltered :: Cxsetter k (Map.Map k a) (Map.Map k a) a Bool
cxfiltered = cxsetter Map.filterWithKey
{-# INLINE cxfiltered #-}

-- | /O(n)/. 'Cxsetter' that simultaneously maps and filters the
-- values of a 'Map.Map'.
--
-- @
-- 'cxsets' cxmapMaybed ≡ 'Data.Map.mapMaybeWithKey'
-- @
--
cxmapMaybed :: Cxsetter k (Map.Map k a) (Map.Map k b) a (Maybe b)
cxmapMaybed = cxsetter Map.mapMaybeWithKey
{-# INLINE cxmapMaybed #-}

-- | /O(n)/. 'Cxtraversal' over the values of a 'Map.Map'.
--
-- Cx dual of 'ixtraversed'. Threads the key as coindex.
--
-- @
-- 'cxtraverseOf' cxtraversed ≡ 'Data.Map.traverseWithKey'
-- @
--
cxtraversed :: Ord k => Cxtraversal k (Map.Map k a) (Map.Map k b) a b
cxtraversed = cxtraversalVl $ \fakb fs ->
  Map.mapWithKey (\k a -> fakb (fmap (Map.! k) fs) k) (copure fs)
{-# INLINE cxtraversed #-}

-- | /O(n)/. 'Cxfold' over the values of a 'Map.Map'.
--
-- Cx dual of 'ixfolded'. Threads the key as coindex.
--
cxfolded :: Ord k => Cxfold k (Map.Map k a) a
cxfolded = cxfoldVl $ \fakb fs ->
  Map.mapWithKey (\k a -> fakb (fmap (Map.! k) fs) k) (copure fs)
{-# INLINE cxfolded #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | /O(1)/. Create a 'Map.Map' from an 'Ixfold'.
--
fromIxfold :: Ord k => Monoid k => AIxfold (Map.Map k a) k s a -> s -> Map.Map k a
fromIxfold o = ixfoldMapOf o Map.singleton
{-# INLINE fromIxfold #-}

---------------------------------------------------------------------
-- Sort-based operators
---------------------------------------------------------------------

-- | Build a 'Map.Map' keyed by lens focus from a list.
--
-- /Benchmark: 1.01x vs direct Map.fromListWith (zero-cost). See "Data.Profunctor.Optic.Bench"./
--
toMapOf :: Ord a => Lens' s a -> [s] -> MapS.Map a [s]
toMapOf _ [] = MapS.empty
toMapOf o xs = MapS.fromListWith (flip (++)) [(s ^. o, [s]) | s <- xs]

-- | Count occurrences per key from a list.
countsOf :: Ord a => Lens' s a -> [s] -> MapS.Map a Int
countsOf _ [] = MapS.empty
countsOf o xs = MapS.fromListWith (+) [(s ^. o, 1 :: Int) | s <- xs]

-- | Sort through a lens, then right-fold each group.
foldSorts :: Ord a => Lens' s a -> (s -> r -> r) -> r -> [s] -> [r]
foldSorts o g z xs = map (foldr g z) (MapS.elems $ toMapOf o xs)

-- | Sort through a lens, then reduce each non-empty group.
foldSorts1 :: Ord a => Lens' s a -> (s -> s -> s) -> [s] -> [s]
foldSorts1 o f xs = map (foldr1 f) (MapS.elems $ toMapOf o xs)

-- | Sort through a lens, then monoidal concat per group.
mconcatSorts :: (Ord a, Monoid m) => Lens' s a -> (s -> m) -> [s] -> [m]
mconcatSorts o g xs = map (foldMap g) (MapS.elems $ toMapOf o xs)

---------------------------------------------------------------------
-- Merge (Sort + containers merge)
---------------------------------------------------------------------

-- | Merge two toListOf through lenses using containers merge tactics.
merges :: Ord a
       => Lens' s a -> Lens' t a
       -> Merge.SimpleWhenMissing a [s] c
       -> Merge.SimpleWhenMissing a [t] c
       -> Merge.SimpleWhenMatched a [s] [t] c
       -> [s] -> [t] -> Map.Map a c
merges lo ro wml wmr wm xs ys =
  Merge.merge wml wmr wm (toMapOf lo xs) (toMapOf ro ys)

-- | Inner merge: only keys present in both inputs.
innerMerges :: Ord a
            => Lens' s a -> Lens' t a
            -> (a -> [s] -> [t] -> c)
            -> [s] -> [t] -> Map.Map a c
innerMerges lo ro f =
  merges lo ro Merge.dropMissing Merge.dropMissing (Merge.zipWithMatched f)

-- | Full outer merge.
outerMerges :: Ord a
            => Lens' s a -> Lens' t a
            -> (a -> [s] -> c) -> (a -> [t] -> c) -> (a -> [s] -> [t] -> c)
            -> [s] -> [t] -> Map.Map a c
outerMerges lo ro fl fr fb =
  merges lo ro (Merge.mapMissing fl) (Merge.mapMissing fr) (Merge.zipWithMatched fb)

-- | Left merge: all keys from left.
leftMerges :: Ord a
           => Lens' s a -> Lens' t a
           -> (a -> [s] -> c) -> (a -> [s] -> [t] -> c)
           -> [s] -> [t] -> Map.Map a c
leftMerges lo ro fl fb =
  merges lo ro (Merge.mapMissing fl) Merge.dropMissing (Merge.zipWithMatched fb)

-- | Right merge: all keys from right.
rightMerges :: Ord a
            => Lens' s a -> Lens' t a
            -> (a -> [t] -> c) -> (a -> [s] -> [t] -> c)
            -> [s] -> [t] -> Map.Map a c
rightMerges lo ro fr fb =
  merges lo ro Merge.dropMissing (Merge.mapMissing fr) (Merge.zipWithMatched fb)

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

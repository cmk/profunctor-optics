{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
-- | Left and right carriers are characterized by their representation
-- functors ('Rep' and 'Corep'). 'Iso' sits at the top where both
-- are trivial ('Identity'). 'Adjoint' sits at the bottom where they
-- form a full adjunction (@'Corep' p ⊣ 'Rep' p@). A left-indexed
-- ('Ix') optic threads an index through the left adjoint functor
-- @(,) k@, while a right-indexed ('Cx') optic threads a coindex
-- through the right adjoint functor @(->) k@.
--
-- Profunctor optics for lazy 'Data.Map.Map'.
--
-- For strict variants, import "Data.Map.Optic".
--
module Data.Map.Lazy.Optic (
    -- * Types
    Map.Map
    -- * Left Adjoint Optics
    -- ** Lens, Ixlens
  , alteredF
  , ixalteredF
    -- ** Traversal, Ixtraversal
  , ixtraversed
    -- ** Traversal0, Ixtraversal0
  , at
  , ixat
  , posAt
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
    -- * Right Adjoint Optics
    -- ** Colens
  , zippedIfKey
    -- ** Cxlens
  , cxzippedIfKey
    -- ** Cotraversal
  , zippedIf
    -- ** Cxtraversal
  , cxtraversed
  , cxzippedIf
    -- ** Cxfold
  , cxfolded
    -- * Adjoint Optics
  , mappedIf
  , ixmappedIf
  , cxmappedIf
  , mappedKey
  , filtered
  , ixfiltered
  , cxfiltered
  , adjusted
  , ixadjusted
  , cxadjusted
  , ixmapped
  , cxmapped
  , altered
  , ixaltered
  , cxaltered
  , updated
  , ixupdated
  , cxupdated
  , ixupdatedLookup
  , cxupdatedLookup
  , updatedMin
  , ixupdatedMin
  , cxupdatedMin
  , updatedMax
  , ixupdatedMax
  , cxupdatedMax
    -- * Operators
    -- ** Sort-based
  , toMapOf
  , countsOf
  , sortFoldOf
  , sortFold1Of
  , sortFoldMapOf
    -- ** Merge (Sort + containers merge)
  , merges
  , mergesInner
  , mergesOuter
  , mergesLeft
  , mergesRight
    -- ** Sort merge tactics
  , sortsWhenMatched
  , sortsWhenMissing
) where

import Data.Profunctor.Optic hiding (filtered, toMapOf, countsOf, sortFoldOf, sortFold1Of, sortFoldMapOf, sortingString, merges, innerMerges, outerMerges, leftMerges, rightMerges, mergesInner, mergesOuter, mergesLeft, mergesRight, sortedMatched, sortedMissing)
import Data.Profunctor.Optic.Import
import Data.Set (Set)
import qualified Data.Map.Lazy as Map
import qualified Data.Map.Merge.Lazy as Merge
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

-- | /O(log n)/. Indexed affine traversal into the value at positional
-- index @i@ (0-based, ascending key order). Returns the key as index.
--
-- Total: returns 'Nothing' when @i@ is out of range.
--
posAt :: Ord k => Int -> Ixtraversal0' k (Map.Map k a) a
posAt i = ixtraversal0' getter setter'
  where
    getter m
      | 0 <= i && i < Map.size m =
          let (k, a) = Map.findMin (Map.drop i m) in Just (k, a)
      | otherwise = Nothing
    setter' m a = case getter m of
      Nothing     -> m
      Just (k, _) -> Map.insert k a m
{-# INLINE posAt #-}

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
validated = fold0 $ \m -> if Map.valid m then Just m else Nothing
{-# INLINE validated #-}

-- | /O(n)/. Adjoint that maps and filters values simultaneously.
--
-- @'sets' 'mappedIf' = 'Map.mapMaybe'@
--
mappedIf :: Adjoint (Map.Map k a) (Map.Map k b) a (Maybe b)
mappedIf = adjoint Map.mapMaybe
{-# INLINE mappedIf #-}

-- | /O(n)/. Indexed adjoint that maps and filters values with key.
--
-- @'ixsets' 'ixmappedIf' = 'Map.mapMaybeWithKey'@
--
ixmappedIf :: Ixadjoint k (Map.Map k a) (Map.Map k b) a (Maybe b)
ixmappedIf = ixadjoint Map.mapMaybeWithKey
{-# INLINE ixmappedIf #-}

-- | /O(n log n)/. Adjoint over the keys of a 'Map.Map'.
--
-- @'sets' 'mappedKey' = 'Map.mapKeys'@
--
mappedKey :: Ord k2 => Adjoint (Map.Map k1 a) (Map.Map k2 a) k1 k2
mappedKey = adjoint Map.mapKeys
{-# INLINE mappedKey #-}

-- | /O(n)/. Filter values.
--
-- @'sets' 'filtered' = 'Map.filter'@
--
filtered :: Adjoint (Map.Map k a) (Map.Map k a) a Bool
filtered = adjoint Map.filter
{-# INLINE filtered #-}

-- | /O(n)/. Filter values with key.
--
-- @'ixsets' 'ixfiltered' = 'Map.filterWithKey'@
--
ixfiltered :: Ixadjoint k (Map.Map k a) (Map.Map k a) a Bool
ixfiltered = ixadjoint Map.filterWithKey
{-# INLINE ixfiltered #-}

-- | /O(log n)/. Adjust a value at a specific key.
--
-- @'sets' ('adjusted' k) = 'Map.adjust' k@
--
adjusted :: Ord k => k -> Adjoint' (Map.Map k a) a
adjusted k = adjoint $ \f -> Map.adjust f k
{-# INLINE adjusted #-}

-- | /O(log n)/. Adjust a value at a specific key, with key available.
--
-- @'ixsets' ('ixadjusted' k) = 'Map.adjustWithKey' k@
--
ixadjusted :: Ord k => k -> Ixadjoint' k (Map.Map k a) a
ixadjusted k = ixadjoint $ \f -> Map.adjustWithKey f k
{-# INLINE ixadjusted #-}

-- | /O(n)/. Map over values.
--
-- @'ixsets' 'ixmapped' = 'Map.mapWithKey'@
--
ixmapped :: Ixadjoint k (Map.Map k a) (Map.Map k b) a b
ixmapped = ixadjoint Map.mapWithKey
{-# INLINE ixmapped #-}

-- | /O(log n)/. Alter the value at a specific key (lazy).
--
-- @'sets' ('altered' k) = 'Map.alter' k@
--
altered :: Ord k => k -> Adjoint' (Map.Map k a) (Maybe a)
altered k = adjoint $ \f -> Map.alter f k
{-# INLINE altered #-}

-- | /O(log n)/. Indexed alter, key available.
--
-- @'ixsets' ('ixaltered' k) f = 'Map.alter' (f k) k@
--
ixaltered :: Ord k => k -> Ixadjoint' k (Map.Map k a) (Maybe a)
ixaltered k = ixadjoint $ \f -> Map.alter (f k) k
{-# INLINE ixaltered #-}

-- | /O(log n)/. Update a value at a specific key. 'Nothing' deletes.
--
-- @'sets' ('updated' k) = 'Map.update' k@
--
updated :: Ord k => k -> Adjoint (Map.Map k a) (Map.Map k a) a (Maybe a)
updated k = adjoint $ \f -> Map.update f k
{-# INLINE updated #-}

-- | /O(log n)/. Update a value at a specific key with key available.
--
-- @'ixsets' ('ixupdated' k) = 'Map.updateWithKey' k@
--
ixupdated :: Ord k => k -> Ixadjoint k (Map.Map k a) (Map.Map k a) a (Maybe a)
ixupdated k = ixadjoint $ \f -> Map.updateWithKey f k
{-# INLINE ixupdated #-}

-- | /O(log n)/. Lookup and update a value at a specific key.
--
-- @'ixsets' ('ixupdatedLookup' k) = 'Map.updateLookupWithKey' k@
--
ixupdatedLookup :: Ord k => k -> Ixadjoint k (Map.Map k a) (Maybe a, Map.Map k a) a (Maybe a)
ixupdatedLookup k = ixadjoint $ \f -> Map.updateLookupWithKey f k
{-# INLINE ixupdatedLookup #-}

-- | /O(log n)/. Update the value at the minimal key. 'Nothing' deletes.
--
-- @'sets' 'updatedMin' = 'Map.updateMin'@
--
updatedMin :: Adjoint (Map.Map k a) (Map.Map k a) a (Maybe a)
updatedMin = adjoint Map.updateMin
{-# INLINE updatedMin #-}

-- | /O(log n)/. Update the value at the minimal key, with key available.
--
-- @'ixsets' 'ixupdatedMin' = 'Map.updateMinWithKey'@
--
ixupdatedMin :: Ixadjoint k (Map.Map k a) (Map.Map k a) a (Maybe a)
ixupdatedMin = ixadjoint Map.updateMinWithKey
{-# INLINE ixupdatedMin #-}

-- | /O(log n)/. Update the value at the maximal key. 'Nothing' deletes.
--
-- @'sets' 'updatedMax' = 'Map.updateMax'@
--
updatedMax :: Adjoint (Map.Map k a) (Map.Map k a) a (Maybe a)
updatedMax = adjoint Map.updateMax
{-# INLINE updatedMax #-}

-- | /O(log n)/. Update the value at the maximal key, with key available.
--
-- @'ixsets' 'ixupdatedMax' = 'Map.updateMaxWithKey'@
--
ixupdatedMax :: Ixadjoint k (Map.Map k a) (Map.Map k a) a (Maybe a)
ixupdatedMax = ixadjoint Map.updateMaxWithKey
{-# INLINE ixupdatedMax #-}

---------------------------------------------------------------------
-- Dual optics
---------------------------------------------------------------------

-- | Colens viewing a 'Map.Map' as a partial function from keys.
--
-- Self-keyed: the key set comes from the focal map (via 'copure').
-- The focus is @k -> Maybe a@ — 'Nothing' for keys absent from a
-- given map. No external key set or default needed.
--
-- @
-- 'zipsWith' 'zippedIf' f m1 m2
-- @
--
-- zips @m1@ and @m2@ over @m2@'s keys (since @'copure' (m1,m2) = m2@
-- for @(,)@). Missing keys in @m1@ appear as 'Nothing'.
--
-- | Colens viewing a 'Map.Map' as a partial function from keys.
-- The focus is @k -> Maybe a@ — 'Nothing' for absent keys.
-- Requires a fixed key set (Colens has no 'copure').
--
zippedIfKey :: Ord k => Set k -> Colens (Map.Map k a) (Map.Map k b) (k -> Maybe a) (k -> Maybe b)
zippedIfKey ks = grate $ \f ->
  Map.mapMaybe id $ Map.fromSet (\k -> f (\m k' -> Map.lookup k' m) k) ks
{-# INLINE zippedIfKey #-}

-- | Coindexed 'Cxlens' with 'Maybe' focus.
-- Requires a fixed key set (Cxlens has no 'copure').
--
cxzippedIfKey :: Ord k => Set k -> Cxlens k (Map.Map k a) (Map.Map k b) (Maybe a) (Maybe b)
cxzippedIfKey ks = cxlensVl $ \fakb fs ->
  Map.mapMaybe id $ Map.fromSet (\k -> fakb (fmap (Map.lookup k) fs) k) ks
{-# INLINE cxzippedIfKey #-}

-- | Pointwise 'Cotraversal' with 'Maybe' focus.
-- Self-keyed: the key set comes from the focal map via 'copure'.
--
zippedIf :: Ord k => Cotraversal (Map.Map k a) (Map.Map k b) (Maybe a) (Maybe b)
zippedIf = cotraversalVl $ \fab fs ->
  let m0 = copure fs
  in  Map.mapMaybe id $ Map.fromSet (\k -> fab (fmap (Map.lookup k) fs)) (Map.keysSet m0)
{-# INLINE zippedIf #-}

-- | Keyed pointwise 'Cxtraversal' with 'Maybe' focus.
-- Self-keyed via 'copure'.
--
cxzippedIf :: Ord k => Cxtraversal k (Map.Map k a) (Map.Map k b) (Maybe a) (Maybe b)
cxzippedIf = cxtraversalVl $ \fakb fs ->
  let m0 = copure fs
  in  Map.mapMaybe id $ Map.fromSet (\k -> fakb (fmap (Map.lookup k) fs) k) (Map.keysSet m0)
{-# INLINE cxzippedIf #-}

---------------------------------------------------------------------
-- Coindexed optics
---------------------------------------------------------------------

-- | /O(n)/. 'Cxadjoint' over the values of a 'Map.Map'.
--
-- Cx dual of 'ixmapped'. Threads the key as coindex on the
-- Costar side, composable with 'Colens' chains.
--
-- @
-- 'cxsets' cxmapped ≡ 'Data.Map.mapWithKey'
-- @
--
cxmapped :: Cxadjoint k (Map.Map k a) (Map.Map k b) a b
cxmapped = cxadjoint Map.mapWithKey
{-# INLINE cxmapped #-}

-- | /O(n)/. 'Cxadjoint' filtering the values of a 'Map.Map'.
--
-- Cx dual of 'ixfiltered'. Keeps entries where the coindexed
-- predicate returns 'True'.
--
-- @
-- 'cxsets' cxfiltered ≡ 'Data.Map.filterWithKey'
-- @
--
cxfiltered :: Cxadjoint k (Map.Map k a) (Map.Map k a) a Bool
cxfiltered = cxadjoint Map.filterWithKey
{-# INLINE cxfiltered #-}

-- | /O(n)/. 'Cxadjoint' that simultaneously maps and filters the
-- values of a 'Map.Map'.
--
-- @
-- 'cxsets' cxmappedIf ≡ 'Data.Map.mapMaybeWithKey'
-- @
--
cxmappedIf :: Cxadjoint k (Map.Map k a) (Map.Map k b) a (Maybe b)
cxmappedIf = cxadjoint Map.mapMaybeWithKey
{-# INLINE cxmappedIf #-}

-- | Cxadjoint wrapping 'Map.adjustWithKey'. Costar dual of 'ixadjusted'.
cxadjusted :: Ord k => k -> Cxadjoint' k (Map.Map k a) a
cxadjusted k = cxadjoint $ \f -> Map.adjustWithKey f k
{-# INLINE cxadjusted #-}

-- | Cxadjoint wrapping 'Map.alter'. Costar dual of 'ixaltered'.
cxaltered :: Ord k => k -> Cxadjoint' k (Map.Map k a) (Maybe a)
cxaltered k = cxadjoint $ \f -> Map.alter (f k) k
{-# INLINE cxaltered #-}

-- | Cxadjoint wrapping 'Map.updateWithKey'. Costar dual of 'ixupdated'.
cxupdated :: Ord k => k -> Cxadjoint k (Map.Map k a) (Map.Map k a) a (Maybe a)
cxupdated k = cxadjoint $ \f -> Map.updateWithKey f k
{-# INLINE cxupdated #-}

-- | Cxadjoint wrapping 'Map.updateLookupWithKey'. Costar dual of 'ixupdatedLookup'.
cxupdatedLookup :: Ord k => k -> Cxadjoint k (Map.Map k a) (Maybe a, Map.Map k a) a (Maybe a)
cxupdatedLookup k = cxadjoint $ \f -> Map.updateLookupWithKey f k
{-# INLINE cxupdatedLookup #-}

-- | Cxadjoint wrapping 'Map.updateMinWithKey'. Costar dual of 'ixupdatedMin'.
cxupdatedMin :: Cxadjoint k (Map.Map k a) (Map.Map k a) a (Maybe a)
cxupdatedMin = cxadjoint Map.updateMinWithKey
{-# INLINE cxupdatedMin #-}

-- | Cxadjoint wrapping 'Map.updateMaxWithKey'. Costar dual of 'ixupdatedMax'.
cxupdatedMax :: Cxadjoint k (Map.Map k a) (Map.Map k a) a (Maybe a)
cxupdatedMax = cxadjoint Map.updateMaxWithKey
{-# INLINE cxupdatedMax #-}

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
  Map.fromSet (\k -> fakb (fmap (Map.! k) fs) k) (Map.keysSet (copure fs))
{-# INLINE cxtraversed #-}

-- | /O(n)/. 'Cxfold' over the values of a 'Map.Map'.
--
-- Cx dual of 'ixfolded'. Threads the key as coindex.
--
cxfolded :: Ord k => Cxfold k (Map.Map k a) a
cxfolded = cxfoldVl $ \fakb fs ->
  Map.fromSet (\k -> fakb (fmap (Map.! k) fs) k) (Map.keysSet (copure fs))
{-# INLINE cxfolded #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

---------------------------------------------------------------------
-- Sort-based operators
---------------------------------------------------------------------

-- | Build a 'Map.Map' mappedKey by lens focus from a list.
--
-- /Benchmark: 1.01x vs direct Map.fromListWith (zero-cost). See "Data.Profunctor.Optic.Bench"./
--
toMapOf :: Ord a => Lens' s a -> [s] -> Map.Map a [s]
toMapOf _ [] = Map.empty
toMapOf o xs = Map.fromListWith (flip (++)) [(s ^. o, [s]) | s <- xs]

-- | Count occurrences per key from a list.
countsOf :: Ord a => Lens' s a -> [s] -> Map.Map a Int
countsOf _ [] = Map.empty
countsOf o xs = Map.fromListWith (+) [(s ^. o, 1 :: Int) | s <- xs]

-- | Sort through a lens, then right-fold each group.
sortFoldOf :: Ord a => Lens' s a -> (s -> r -> r) -> r -> [s] -> [r]
sortFoldOf o g z xs = map (foldr g z) (Map.elems $ toMapOf o xs)

-- | Sort through a lens, then reduce each non-empty group.
sortFold1Of :: Ord a => Lens' s a -> (s -> s -> s) -> [s] -> [s]
sortFold1Of o f xs = map (foldr1 f) (Map.elems $ toMapOf o xs)

-- | Sort through a lens, then monoidal concat per group.
sortFoldMapOf :: (Ord a, Monoid m) => Lens' s a -> (s -> m) -> [s] -> [m]
sortFoldMapOf o g xs = map (foldMap g) (Map.elems $ toMapOf o xs)

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
mergesInner :: Ord a
            => Lens' s a -> Lens' t a
            -> Merge.SimpleWhenMatched a [s] [t] c
            -> [s] -> [t] -> Map.Map a c
mergesInner lo ro wm =
  merges lo ro Merge.dropMissing Merge.dropMissing wm

-- | Full outer merge.
mergesOuter :: Ord a
            => Lens' s a -> Lens' t a
            -> Merge.SimpleWhenMissing a [s] c
            -> Merge.SimpleWhenMissing a [t] c
            -> Merge.SimpleWhenMatched a [s] [t] c
            -> [s] -> [t] -> Map.Map a c
mergesOuter = merges

-- | Left merge: all keys from left, matched keys from both.
mergesLeft :: Ord a
           => Lens' s a -> Lens' t a
           -> Merge.SimpleWhenMissing a [s] c
           -> Merge.SimpleWhenMatched a [s] [t] c
           -> [s] -> [t] -> Map.Map a c
mergesLeft lo ro wml wm =
  merges lo ro wml Merge.dropMissing wm

-- | Right merge: all keys from right, matched keys from both.
mergesRight :: Ord a
            => Lens' s a -> Lens' t a
            -> Merge.SimpleWhenMissing a [t] c
            -> Merge.SimpleWhenMatched a [s] [t] c
            -> [s] -> [t] -> Map.Map a c
mergesRight lo ro wmr wm =
  merges lo ro Merge.dropMissing wmr wm

---------------------------------------------------------------------
-- Sort merge tactics
---------------------------------------------------------------------

-- | Construct a 'WhenMatched' merge tactic from a 'Sort'.
-- Uses @i = ()@ (one position per key).
sortsWhenMatched :: Sort () k (x, y) z -> Merge.SimpleWhenMatched k x y z
sortsWhenMatched (Sort h) = Merge.zipWithMatched $ \k x y ->
  h (const (k, (x, y)))

-- | Construct a 'WhenMissing' merge tactic from a 'Sort'.
-- Uses @i = ()@ (one position per key).
sortsWhenMissing :: Sort () k x y -> Merge.SimpleWhenMissing k x y
sortsWhenMissing (Sort h) = Merge.mapMissing $ \k x ->
  h (const (k, x))

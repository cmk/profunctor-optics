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
-- Profunctor optics for 'Data.IntMap.IntMap'.
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
  , adjusted
  , ixmapped
  , ixfiltered
  , altered
  , altered'
  , ixaltered
  , ixaltered'
    -- * Dual Optics
    -- ** Colens
  , zippedIf
    -- ** Cxlens
  , cxzippedIf
    -- ** Cotraversal
  , zippedTraverseIf
    -- ** Cxtraversal
  , cxtraversed
  , cxzippedTraverseIf
    -- ** Cxsetter
  , cxmapped
  , cxfiltered
  , cxmappedIf
    -- ** Cxfold
  , cxfolded
    -- * Operators
  , toIntMapOf
  , countsOf
    -- ** Sort-based
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

import Data.Profunctor.Optic hiding (toMapOf, countsOf, sortFoldOf, sortFold1Of, sortFoldMapOf, sortingString, merges, innerMerges, outerMerges, leftMerges, rightMerges, sortedMatched, sortedMissing)
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

-- | /O(log n)/. Indexed lens into Maybe of a value at the incoming
-- index. The index serves as both the optic index and the 'IntMap' key.
--
ixalteredF :: Ixlens' (Sum Int) (IM.IntMap a) (Maybe a)
ixalteredF = ixlensVl $ \f k -> IM.alterF (f k) (getSum k)
{-# INLINE ixalteredF #-}

-- | /O(n)/. 'Ixtraversal' over values.
--
ixtraversed :: Ixtraversal (Sum Int) (IM.IntMap a) (IM.IntMap b) a b
ixtraversed = ixtraversalVl $ \kab k -> IM.traverseWithKey (\i -> kab (k <> Sum i))
{-# INLINE ixtraversed #-}

-- | /O(log n)/. Affine traversal into the value at a key.
--
at :: Int -> Traversal0' (IM.IntMap a) a
at k = traversal0' (IM.lookup k) (flip $ IM.insert k)
{-# INLINE at #-}

-- | /O(log n)/. Indexed affine traversal into the value at the incoming index.
--
ixat :: Ixtraversal0' (Sum Int) (IM.IntMap a) a
ixat = ixtraversalVl0 $ \point f k s -> case IM.lookup (getSum k) s of
  Nothing -> point s
  Just a  -> fmap (\b -> IM.insert (getSum k) b s) (f k a)
{-# INLINE ixat #-}

-- | /O(log n)/. Update a value at the incoming index.
--
updated :: Ixsetter (Sum Int) (IM.IntMap a) (IM.IntMap a) a (Maybe a)
updated = ixsetter $ \f k -> IM.updateWithKey (\i -> f (Sum i)) (getSum k)
{-# INLINE updated #-}

-- | /O(log n)/. Indexed affine traversal into the value at the largest key smaller than the incoming index.
--
lookedLT :: Ixtraversal0' (Sum Int) (IM.IntMap a) a
lookedLT = ixtraversalVl0 $ \point f k s ->
  maybe (point s) (\(i, a) -> fmap (\b -> IM.insert i b s) (f (Sum i) a)) (IM.lookupLT (getSum k) s)
{-# INLINE lookedLT #-}

-- | /O(log n)/. Indexed affine traversal into the value at the largest key smaller than or equal to the incoming index.
--
lookedLE :: Ixtraversal0' (Sum Int) (IM.IntMap a) a
lookedLE = ixtraversalVl0 $ \point f k s ->
  maybe (point s) (\(i, a) -> fmap (\b -> IM.insert i b s) (f (Sum i) a)) (IM.lookupLE (getSum k) s)
{-# INLINE lookedLE #-}

-- | /O(log n)/. Indexed affine traversal into the value at the smallest key greater than or equal to the incoming index.
--
lookedGE :: Ixtraversal0' (Sum Int) (IM.IntMap a) a
lookedGE = ixtraversalVl0 $ \point f k s ->
  maybe (point s) (\(i, a) -> fmap (\b -> IM.insert i b s) (f (Sum i) a)) (IM.lookupGE (getSum k) s)
{-# INLINE lookedGE #-}

-- | /O(log n)/. Indexed affine traversal into the value at the smallest key greater than the incoming index.
--
lookedGT :: Ixtraversal0' (Sum Int) (IM.IntMap a) a
lookedGT = ixtraversalVl0 $ \point f k s ->
  maybe (point s) (\(i, a) -> fmap (\b -> IM.insert i b s) (f (Sum i) a)) (IM.lookupGT (getSum k) s)
{-# INLINE lookedGT #-}

-- | /O(n)/. 'Fold' over all values in ascending key order.
--
values :: Fold (IM.IntMap a) a
values = fold_ IM.toAscList . second'
{-# INLINE values #-}

-- | /O(n)/. 'Ixfold' over values.
--
ixfolded :: Ixfold (Sum Int) (IM.IntMap a) a
ixfolded = ixfoldVl $ \kab k -> IM.traverseWithKey (\i -> kab (k <> Sum i))
{-# INLINE ixfolded #-}

-- | /O(log n)/. 'Ixfold0' into the value at the minimal key.
--
lookedMin :: Ixfold0 (Sum Int) (IM.IntMap a) a
lookedMin = ixfold0 $ fmap (\(i, a) -> (Sum i, a)) . IM.lookupMin
{-# INLINE lookedMin #-}

-- | /O(log n)/. 'Ixfold0' into the value at the maximal key.
--
lookedMax :: Ixfold0 (Sum Int) (IM.IntMap a) a
lookedMax = ixfold0 $ fmap (\(i, a) -> (Sum i, a)) . IM.lookupMax
{-# INLINE lookedMax #-}

-- | /O(log n)/. Adjust a value at the incoming index.
--
adjusted :: Ixsetter' (Sum Int) (IM.IntMap a) a
adjusted = ixsetter $ \f k -> IM.adjust (f k) (getSum k)
{-# INLINE adjusted #-}

-- | /O(n)/. 'Ixsetter' over values.
--
ixmapped :: Ixsetter (Sum Int) (IM.IntMap a) (IM.IntMap b) a b
ixmapped = ixsetter $ \f k -> IM.mapWithKey (\i -> f (k <> Sum i))
{-# INLINE ixmapped #-}

-- | /O(n)/. 'Ixsetter' filtering values.
--
ixfiltered :: Ixsetter (Sum Int) (IM.IntMap a) (IM.IntMap a) a Bool
ixfiltered = ixsetter $ \f k -> IM.filterWithKey (\i -> f (k <> Sum i))
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
ixaltered :: Ixsetter' (Sum Int) (IM.IntMap a) (Maybe a)
ixaltered = ixsetter $ \f k -> IML.alter (f k) (getSum k)
{-# INLINE ixaltered #-}

-- | /O(log n)/. Indexed alter (strict, values forced on insert).
--
ixaltered' :: Ixsetter' (Sum Int) (IM.IntMap a) (Maybe a)
ixaltered' = ixsetter $ \f k -> IM.alter (f k) (getSum k)
{-# INLINE ixaltered' #-}

---------------------------------------------------------------------
-- Dual optics
---------------------------------------------------------------------

-- | Colens viewing an 'IM.IntMap' as a partial function from keys.
-- The focus is @Int -> Maybe a@ — 'Nothing' for absent keys.
-- Requires a fixed key set (Colens has no 'copure').
--
zippedIf :: IntSet -> Colens (IM.IntMap a) (IM.IntMap b) (Int -> Maybe a) (Int -> Maybe b)
zippedIf ks = grate $ \f ->
  IM.mapMaybe id $ IM.fromSet (\k -> f (\m k' -> IM.lookup k' m) k) ks
{-# INLINE zippedIf #-}

-- | Coindexed 'Cxlens' with 'Maybe' focus.
-- Requires a fixed key set (Cxlens has no 'copure').
--
cxzippedIf :: IntSet -> Cxlens (Sum Int) (IM.IntMap a) (IM.IntMap b) (Maybe a) (Maybe b)
cxzippedIf ks = cxlensVl $ \fakb k fs ->
  IM.mapMaybe id $ IM.fromSet (\i -> fakb (fmap (IM.lookup i) fs) (k <> Sum i)) ks
{-# INLINE cxzippedIf #-}

-- | Pointwise 'Cotraversal' with 'Maybe' focus.
-- Self-keyed: the key set comes from the focal map via 'copure'.
--
zippedTraverseIf :: Cotraversal (IM.IntMap a) (IM.IntMap b) (Maybe a) (Maybe b)
zippedTraverseIf = cotraversalVl $ \fab fs ->
  let m0 = copure fs
  in  IM.mapMaybe id $ IM.fromSet (\k -> fab (fmap (IM.lookup k) fs)) (IM.keysSet m0)
{-# INLINE zippedTraverseIf #-}

-- | Keyed pointwise 'Cxtraversal' with 'Maybe' focus.
-- Self-keyed via 'copure'.
--
cxzippedTraverseIf :: Cxtraversal (Sum Int) (IM.IntMap a) (IM.IntMap b) (Maybe a) (Maybe b)
cxzippedTraverseIf = cxtraversalVl $ \fakb k fs ->
  let m0 = copure fs
  in  IM.mapMaybe id $ IM.fromSet (\i -> fakb (fmap (IM.lookup i) fs) (k <> Sum i)) (IM.keysSet m0)
{-# INLINE cxzippedTraverseIf #-}

---------------------------------------------------------------------
-- Coindexed optics
---------------------------------------------------------------------

-- | /O(n)/. 'Cxsetter' over the values of an 'IM.IntMap'.
--
-- Cx dual of 'ixmapped'. Threads the key as coindex on the
-- Costar side, composable with 'Colens' chains.
--
-- @
-- 'cxsets' cxmapped ≡ 'Data.IntMap.mapWithKey'
-- @
--
cxmapped :: Cxsetter (Sum Int) (IM.IntMap a) (IM.IntMap b) a b
cxmapped = cxsetter $ \f k -> IM.mapWithKey (\i -> f (k <> Sum i))
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
cxfiltered :: Cxsetter (Sum Int) (IM.IntMap a) (IM.IntMap a) a Bool
cxfiltered = cxsetter $ \f k -> IM.filterWithKey (\i -> f (k <> Sum i))
{-# INLINE cxfiltered #-}

-- | /O(n)/. 'Cxsetter' that simultaneously maps and filters the
-- values of an 'IM.IntMap'.
--
-- @
-- 'cxsets' cxmappedIf ≡ 'Data.IntMap.mapMaybeWithKey'
-- @
--
cxmappedIf :: Cxsetter (Sum Int) (IM.IntMap a) (IM.IntMap b) a (Maybe b)
cxmappedIf = cxsetter $ \f k -> IM.mapMaybeWithKey (\i -> f (k <> Sum i))
{-# INLINE cxmappedIf #-}

-- | /O(n)/. 'Cxtraversal' over the values of an 'IM.IntMap'.
--
-- Cx dual of 'ixtraversed'. Threads the key as coindex.
--
-- @
-- 'cxtraverseOf' cxtraversed ≡ 'Data.IntMap.traverseWithKey'
-- @
--
cxtraversed :: Cxtraversal (Sum Int) (IM.IntMap a) (IM.IntMap b) a b
cxtraversed = cxtraversalVl $ \fakb k fs ->
  IM.mapWithKey (\i a -> fakb (fmap (IM.findWithDefault a i) fs) (k <> Sum i)) (copure fs)
{-# INLINE cxtraversed #-}

-- | /O(n)/. 'Cxfold' over the values of an 'IM.IntMap'.
--
-- Cx dual of 'ixfolded'. Threads the key as coindex.
--
cxfolded :: Cxfold (Sum Int) (IM.IntMap a) a
cxfolded = cxfoldVl $ \fakb k fs ->
  IM.mapWithKey (\i a -> fakb (fmap (IM.findWithDefault a i) fs) (k <> Sum i)) (copure fs)
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
sortFoldOf :: Lens' s Int -> (s -> r -> r) -> r -> [s] -> [r]
sortFoldOf o g z xs = map (foldr g z) (IM.elems $ toIntMapOf o xs)

-- | Sort through an Int lens, then reduce each non-empty group.
sortFold1Of :: Lens' s Int -> (s -> s -> s) -> [s] -> [s]
sortFold1Of o f xs = map (foldr1 f) (IM.elems $ toIntMapOf o xs)

-- | Sort through an Int lens, then monoidal concat per group.
sortFoldMapOf :: Monoid m => Lens' s Int -> (s -> m) -> [s] -> [m]
sortFoldMapOf o g xs = map (foldMap g) (IM.elems $ toIntMapOf o xs)

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
mergesInner :: Lens' s Int -> Lens' t Int
            -> Merge.SimpleWhenMatched [s] [t] c
            -> [s] -> [t] -> IM.IntMap c
mergesInner lo ro wm =
  merges lo ro Merge.dropMissing Merge.dropMissing wm

-- | Full outer merge.
mergesOuter :: Lens' s Int -> Lens' t Int
            -> Merge.SimpleWhenMissing [s] c
            -> Merge.SimpleWhenMissing [t] c
            -> Merge.SimpleWhenMatched [s] [t] c
            -> [s] -> [t] -> IM.IntMap c
mergesOuter = merges

-- | Left merge: all keys from left, matched keys from both.
mergesLeft :: Lens' s Int -> Lens' t Int
           -> Merge.SimpleWhenMissing [s] c
           -> Merge.SimpleWhenMatched [s] [t] c
           -> [s] -> [t] -> IM.IntMap c
mergesLeft lo ro wml wm =
  merges lo ro wml Merge.dropMissing wm

-- | Right merge: all keys from right, matched keys from both.
mergesRight :: Lens' s Int -> Lens' t Int
            -> Merge.SimpleWhenMissing [t] c
            -> Merge.SimpleWhenMatched [s] [t] c
            -> [s] -> [t] -> IM.IntMap c
mergesRight lo ro wmr wm =
  merges lo ro Merge.dropMissing wmr wm

---------------------------------------------------------------------
-- Sort merge tactics
---------------------------------------------------------------------

-- | Construct a 'WhenMatched' merge tactic from a 'Sort'.
-- Uses @i = ()@ (one position per key).
sortsWhenMatched :: Sort () Int (x, y) z -> Merge.SimpleWhenMatched x y z
sortsWhenMatched (Sort h) = Merge.zipWithMatched $ \k x y ->
  h (const (k, (x, y)))

-- | Construct a 'WhenMissing' merge tactic from a 'Sort'.
-- Uses @i = ()@ (one position per key).
sortsWhenMissing :: Sort () Int x y -> Merge.SimpleWhenMissing x y
sortsWhenMissing (Sort h) = Merge.mapMissing $ \k x ->
  h (const (k, x))

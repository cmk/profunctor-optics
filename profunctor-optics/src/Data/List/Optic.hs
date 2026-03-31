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
module Data.List.Optic (
    -- * Optics
    -- ** Traversal0, Ixtraversal0
    at
  , ixat
    -- ** Traversal, Ixtraversal
  , traversed
  , ixtraversed
    -- ** Fold, Ixfold
  , folded
  , ixfolded
    -- ** Setter, Ixsetter
  , fmapped
  , ixmapped
  , ixfiltered
    -- * Dual Optics
    -- ** Colens
  , zipped
    -- ** Cosetter
  , zipListed
    -- ** Cxsetter
  , cxmapped
    -- ** Cxfold
  , cxfolded
    -- * Operators
    -- * Sort-based operators (Lens, Ord)
  , sortsOf
  , sortsDescOf
  , groupsOf
  , nubsOf
  , sortsString
    -- * Comparator-based operators (*By)
  , groupSortBy
  , groupSort
  , groupSortOn
  , monoidSortBy
  , monoidSort
  , monoidSortOn
  , uniqueSortBy
  , uniqueSort
  , uniqueSortOn
) where

import Data.Profunctor.Optic hiding (zipped, sorts, sortsDesc, groups, nubs, sortingString)
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Sort (sortingRep)
import Data.Maybe (fromMaybe, listToMaybe)
import Data.Ord (Down(..), comparing)
import qualified Data.List as L
import qualified Data.Map.Strict as Map
import Prelude

-- | /O(n)/. Affine traversal into the value at an index of a list.
--
at :: Int -> Traversal0' [a] a
at k = traversalVl0 $ \point f xs -> if k < 0 then point xs else
  let go [] _ = point []
      go (a:as) 0 = (:as) <$> f a
      go (a:as) i = (a:) <$> (go as $! i - 1)
   in go xs k
{-# INLINE at #-}

-- | /O(n)/. Indexed affine traversal into the value at an index.
--
ixat :: Ixtraversal0' (Sum Int) [a] a
ixat = ixtraversalVl0 $ \point f k s ->
  case listToMaybe [(n, x) | (n, x) <- zip [0..] s, n == getSum k] of
    Nothing     -> point s
    Just (_, a) -> fmap (\b -> zipWith (\j x -> if getSum k == j then b else x) [0..] s) (f k a)
{-# INLINE ixat #-}

-- | /O(n)/. 'Ixtraversal' over the values of a list.
--
ixtraversed :: Ixtraversal (Sum Int) [a] [b] a b
ixtraversed = ixtraversalVl $ \f k -> traverse (\(i, a) -> f (k <> Sum i) a) . zip [0..]
{-# INLINE ixtraversed #-}

-- | /O(n)/. 'Ixfold' over the values of a list.
--
ixfolded :: Ixfold (Sum Int) [a] a
ixfolded = ixfoldVl $ \f k -> traverse (\(i, a) -> f (k <> Sum i) a) . zip [0..]
{-# INLINE ixfolded #-}

-- | /O(n)/. 'Ixsetter' over the values of a list.
--
ixmapped :: Ixsetter (Sum Int) [a] [b] a b
ixmapped = ixsetter $ \f -> zipWith (\i -> f (Sum i)) [0..]
{-# INLINE ixmapped #-}

-- | /O(n)/. 'Ixsetter' filtering the values of a list.
--
ixfiltered :: Ixsetter (Sum Int) [a] [a] a Bool
ixfiltered = ixsetter $ \f xs -> [x | (i, x) <- zip [0..] xs, f (Sum i) x]
{-# INLINE ixfiltered #-}

---------------------------------------------------------------------
-- Dual optics
---------------------------------------------------------------------

-- | Colens for lists of known length. Zips pointwise.
-- Requires known length to be representable.
--
zipped :: Int -> Colens [a] [b] a b
zipped n = grate $ \f -> [f (\xs -> xs !! i) | i <- [0 .. n - 1]]
{-# INLINE zipped #-}

---------------------------------------------------------------------
-- Coindexed optics
---------------------------------------------------------------------

-- | /O(n)/. 'Cxsetter' over the values of a list.
--
-- Cx dual of 'ixmapped'. Threads the positional index as coindex
-- on the Costar side.
--
-- @
-- 'cxsets' cxmapped ≡ \\f xs -> 'zipWith' (\\i a -> f i a) [0..] xs
-- @
--
cxmapped :: Cxsetter (Sum Int) [a] [b] a b
cxmapped = cxsetter $ \f xs -> zipWith (\i a -> f (Sum i) a) [0..] xs
{-# INLINE cxmapped #-}

-- | /O(n^2)/. 'Cxfold' over the elements of a list.
--
-- Cx dual of 'ixfolded'. Threads the positional index as coindex.
--
-- __Performance note__: /O(n^2)/ due to @('!!')@ lookups. For
-- performance-sensitive code, convert to @Seq@ or @IntMap@ and use
-- their /O(n log n)/ 'Data.Sequence.Optic.cxfolded' or
-- 'Data.IntMap.Optic.cxfolded' instead.
--
cxfolded :: Cxfold (Sum Int) [a] a
cxfolded = cxfoldVl $ \fakb k fs ->
  zipWith (\i a -> fakb (fmap (\s -> fromMaybe a (listToMaybe (drop i s))) fs) (k <> Sum i)) [0..] (copure fs)
{-# INLINE cxfolded #-}

---------------------------------------------------------------------
-- Sort-based operators
---------------------------------------------------------------------

-- | Sort a list through a lens. Returns @[]@ on empty input.
--
-- /Benchmark: 1.01x vs direct Map.fromListWith (zero-cost). See "Data.Profunctor.Optic.Bench"./
--
sortsOf :: Ord a => Lens' s a -> [s] -> [[s]]
sortsOf _ [] = []
sortsOf o xs = Map.elems $ Map.fromListWith (flip (++))
  [(s ^. o, [s]) | s <- xs]

-- | Sort a list in descending order through a lens.
sortsDescOf :: Ord a => Lens' s a -> [s] -> [[s]]
sortsDescOf _ [] = []
sortsDescOf o xs = Map.elems $ Map.fromListWith (flip (++))
  [(Down (s ^. o), [s]) | s <- xs]

-- | Group a list through a lens.
groupsOf :: Ord a => Lens' s a -> [s] -> [[s]]
groupsOf = sortsOf

-- | Deduplicate a list through a lens, keeping first per group.
nubsOf :: Ord a => Lens' s a -> [s] -> [s]
nubsOf _ [] = []
nubsOf o xs = map head $ sortsOf o xs

-- | Sort a 'String' by a key on each character.
sortsString :: Ord k => (Char -> k) -> String -> Map.Map k String
sortsString = sortingRep length (\s i -> s !! i) id

---------------------------------------------------------------------
-- Comparator-based operators (*By)
---------------------------------------------------------------------

-- | Sort a list with a stable sort, grouping equal elements.
--
-- The core primitive: sort by comparator, then aggregate runs of
-- equal elements with the grouping function.
--
-- @
-- 'groupSortBy' compare (\\x xs -> x : xs) = 'Data.List.sortBy' compare . 'Data.List.group'
-- @
--
groupSortBy :: (a -> a -> Ordering)  -- ^ comparator
            -> (a -> [a] -> b)       -- ^ grouper: head + rest → result
            -> [a] -> [b]
groupSortBy cmp grp = aggregate . L.sortBy cmp
  where
    aggregate []    = []
    aggregate (h:t) = g `seq` g : aggregate rst
      where
        g         = grp h eqs
        (eqs,rst) = span (\x -> cmp x h /= GT) t

-- | Sort a list, grouping equal elements.
--
-- @
-- 'groupSort' (\\x xs -> x : xs) [3,1,2,1,3] = [[1,1],[2],[3,3]]
-- @
--
groupSort :: Ord a => (a -> [a] -> b) -> [a] -> [b]
groupSort = groupSortBy compare

-- | Sort by a projection function, grouping equal elements.
--
-- @
-- 'groupSortOn' 'fst' (\\k x xs -> (k, x : map snd xs)) [(2,'b'),(1,'a'),(2,'c')]
--   = [(1,\"a\"),(2,\"bc\")]
-- @
--
groupSortOn :: Ord k
            => (a -> k)              -- ^ projection
            -> (k -> a -> [a] -> b)  -- ^ grouper with key
            -> [a] -> [b]
groupSortOn key grp = groupSortBy (comparing fst) grp_val . map inj
  where
    grp_val (k, a) kas = grp k a (map snd kas)
    inj x = k `seq` (k, x) where k = key x

-- | Sort by comparator, aggregating duplicates with the monoid.
monoidSortBy :: Monoid a => (a -> a -> Ordering) -> [a] -> [a]
monoidSortBy cmp = groupSortBy cmp (\x xs -> x <> mconcat xs)

-- | Sort, aggregating duplicates with the monoid.
--
-- @
-- 'monoidSort' [Sum 1, Sum 2, Sum 1] = [Sum 2, Sum 2]
-- @
--
monoidSort :: (Monoid a, Ord a) => [a] -> [a]
monoidSort = monoidSortBy compare

-- | Sort by projection, aggregating duplicates with the monoid.
monoidSortOn :: (Monoid a, Ord k) => (a -> k) -> [a] -> [a]
monoidSortOn key = groupSortOn key (\_ x xs -> x <> mconcat xs)

-- | Sort by comparator, discarding duplicates (keeps first).
uniqueSortBy :: (a -> a -> Ordering) -> [a] -> [a]
uniqueSortBy cmp = groupSortBy cmp const

-- | Sort, discarding duplicates.
--
-- @
-- 'uniqueSort' [3,1,2,1,3] = [1,2,3]
-- @
--
uniqueSort :: Ord a => [a] -> [a]
uniqueSort = uniqueSortBy compare

-- | Sort by projection, discarding duplicates (keeps first).
uniqueSortOn :: Ord k => (a -> k) -> [a] -> [a]
uniqueSortOn key = groupSortOn key (\_ x _ -> x)

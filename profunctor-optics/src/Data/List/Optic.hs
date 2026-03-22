{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.List.Optic (
    -- * Optics
    -- ** Traversal0, Ixtraversal0
    at
  , ixat
    -- ** Traversal, Ixtraversal
  , ixtraversed
    -- ** Fold, Ixfold
  , ixfolded
    -- ** Setter, Ixsetter
  , ixmapped
  , ixfiltered
    -- * Operators
    -- * Sort-based operators (Lens, Ord)
  , sortingOf
  , sortingDescOf
  , groupingOf
  , nubbingOf
  , sortingString
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

import Data.Profunctor.Optic hiding (sortingOf, sortingDescOf, groupingOf, nubbingOf, sortingString)
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Sort (sortingRep)
import Data.Maybe (listToMaybe)
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
ixat :: Int -> Ixtraversal0' Int [a] a
ixat i = ixtraversal0' f g
  where
    f s = listToMaybe [(n, x) | (n, x) <- zip [0..] s, n == i]
    g s a = zipWith (\j x -> if i == j then a else x) [0..] s
{-# INLINE ixat #-}

-- | /O(n)/. 'Ixtraversal' over the values of a list.
--
ixtraversed :: Ixtraversal Int [a] [b] a b
ixtraversed = ixtraversalVl $ \f -> traverse (uncurry f) . zip [0..]
{-# INLINE ixtraversed #-}

-- | /O(n)/. 'Ixfold' over the values of a list.
--
ixfolded :: Ixfold Int [a] a
ixfolded = ixfoldVl $ \f -> traverse (uncurry f) . zip [0..]
{-# INLINE ixfolded #-}

-- | /O(n)/. 'Ixsetter' over the values of a list.
--
ixmapped :: Ixsetter Int [a] [b] a b
ixmapped = ixsetter $ \f -> zipWith f [0..]
{-# INLINE ixmapped #-}

-- | /O(n)/. 'Ixsetter' filtering the values of a list.
--
ixfiltered :: Ixsetter Int [a] [a] a Bool
ixfiltered = ixsetter $ \f xs -> [x | (i, x) <- zip [0..] xs, f i x]
{-# INLINE ixfiltered #-}

---------------------------------------------------------------------
-- Sort-based operators
---------------------------------------------------------------------

-- | Sort a list through a lens. Returns @[]@ on empty input.
--
-- /Benchmark: 1.01x vs direct Map.fromListWith (zero-cost). See "Data.Profunctor.Optic.Bench"./
--
sortingOf :: Ord a => Lens' s a -> [s] -> [[s]]
sortingOf _ [] = []
sortingOf o xs = Map.elems $ Map.fromListWith (flip (++))
  [(s ^. o, [s]) | s <- xs]

-- | Sort a list in descending order through a lens.
sortingDescOf :: Ord a => Lens' s a -> [s] -> [[s]]
sortingDescOf _ [] = []
sortingDescOf o xs = Map.elems $ Map.fromListWith (flip (++))
  [(Down (s ^. o), [s]) | s <- xs]

-- | Group a list through a lens.
groupingOf :: Ord a => Lens' s a -> [s] -> [[s]]
groupingOf = sortingOf

-- | Deduplicate a list through a lens, keeping first per group.
nubbingOf :: Ord a => Lens' s a -> [s] -> [s]
nubbingOf _ [] = []
nubbingOf o xs = map head $ sortingOf o xs

-- | Sort a 'String' by a key on each character.
sortingString :: Ord k => (Char -> k) -> String -> Map.Map k String
sortingString = sortingRep length (\s i -> s !! i) id

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

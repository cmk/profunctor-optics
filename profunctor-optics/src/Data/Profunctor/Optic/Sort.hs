-- | Sort carriers and generic representable sort functions.
--
-- The 'Sort' type and combinators live in
-- "Data.Profunctor.Optic.Carrier". Lens-based sort operators
-- live in "Data.List.Optic" and "Data.Map.Optic".
module Data.Profunctor.Optic.Sort (
    -- * Re-exports from Carrier
    Sort(..)
  , runSort
  , (%.)
  , bindSort
  , catSort
  , sortC
  , remapSort
  , eitherSort
  , maybeSort
  , zipsSorting

    -- * Sort carriers (Ord, Map)
  , mkSort
  , mkSortN

    -- * Generic representable sort
  , sortingRep
  , sortUniqueRep
  , sortTaggedRep
  , groupTaggedRep

    -- * Lens-based operators (List)
  , sorts
  , sortsDesc
  , groups
  , nubs

    -- * Container construction (List)
  , toMapOf
  , countsOf

    -- * Post-sort foldMapOf (List)
  , foldSorts
  , foldSorts1
  , mconcatSorts

    -- * Sort as String sort
  , sortingString

    -- * Merge (Sort + containers merge)
  , merges
  , innerMerges
  , outerMerges
  , leftMerges
  , rightMerges

    -- * Sort merge tactics
  , sortedMatched
  , sortedMissing
) where

import Data.Ord (Down(..))
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Types (Lens')
import Data.Profunctor.Optic.View (view)
import Prelude (Int, Ord, Bounded, Enum, Eq, seq,
                (+), (-), head, map, fst, snd, length, const, (.), ($), flip, fmap, foldMap, foldr, foldr1, (++))

import qualified Data.Map.Strict as Map
import qualified Data.Map.Merge.Strict as Merge

---------------------------------------------------------------------
-- Sort carriers (Ord, Map)
---------------------------------------------------------------------

-- | Identity carrier for finite index types.
-- Groups by key, producing a 'Map' of toListOf.
mkSort :: (Bounded i, Enum i, Ord k) => Sort i k a (Map.Map k [a])
mkSort = Sort $ \inp ->
  Map.fromListWith (flip (++)) [ ki `seq` a `seq` (ki, [a])
                                | i <- [minBound..maxBound]
                                , let (ki, a) = inp i ]
{-# INLINEABLE mkSort #-}

-- | Identity carrier for Int-indexed containers of known size.
--
-- /Benchmark: 0.90–0.99x vs direct Map.fromListWith (zero-cost). See "Data.Profunctor.Optic.Bench"./
--
mkSortN :: Ord k => Int -> Sort Int k a (Map.Map k [a])
mkSortN n = Sort $ \inp ->
  Map.fromListWith (flip (++)) [ ki `seq` a `seq` (ki, [a])
                                | i <- [0..n-1]
                                , let (ki, a) = inp i ]
{-# INLINEABLE mkSortN #-}

---------------------------------------------------------------------
-- Generic representable sort
---------------------------------------------------------------------

-- | Sort any @Int@-indexed representable container by key.
sortingRep :: Ord k
           => (c -> Int) -> (c -> Int -> a) -> ([a] -> c')
           -> (a -> k) -> c -> Map.Map k c'
sortingRep len idx build key c =
  let n = len c
      result = runSort (mkSortN n) (\i -> (key (idx c i), idx c i))
  in  fmap build result
{-# INLINE sortingRep #-}

-- | Sort + deduplicate: keep first element per key.
sortUniqueRep :: Ord k
              => (c -> Int) -> (c -> Int -> a) -> (a -> c')
              -> (a -> k) -> c -> Map.Map k c'
sortUniqueRep len idx build key c =
  fmap (build . head) $ sortingRep len idx id key c
{-# INLINE sortUniqueRep #-}

-- | Tagged sort: sort keys + permute values in tandem.
sortTaggedRep :: Ord k
              => (ck -> Int) -> (ck -> Int -> k) -> (cv -> Int -> v)
              -> ([k] -> ck') -> ([v] -> cv')
              -> ck -> cv -> Map.Map k (ck', cv')
sortTaggedRep klen kidx vidx kbuild vbuild ks vs =
  let n = klen ks
      result = runSort (mkSortN n) (\i -> (kidx ks i, (kidx ks i, vidx vs i)))
  in  fmap (\pairs -> (kbuild (map fst pairs), vbuild (map snd pairs))) result
{-# INLINE sortTaggedRep #-}

-- | Group by key, returning Map from keys to value containers.
groupTaggedRep :: Ord k
               => (ck -> Int) -> (ck -> Int -> k) -> (cv -> Int -> v)
               -> ([v] -> cv') -> ck -> cv -> Map.Map k cv'
groupTaggedRep klen kidx vidx vbuild ks vs =
  let n = klen ks
      result = runSort (mkSortN n) (\i -> (kidx ks i, vidx vs i))
  in  fmap vbuild result
{-# INLINE groupTaggedRep #-}

---------------------------------------------------------------------
-- Lens-based operators (List)
---------------------------------------------------------------------

-- | Sort a list through a lens. Returns @[]@ on empty input.
sorts :: Ord a => Lens' s a -> [s] -> [[s]]
sorts _ [] = []
sorts o xs = Map.elems $ Map.fromListWith (flip (++))
  [(view o s, [s]) | s <- xs]

-- | Sort a list in descending order through a lens.
sortsDesc :: Ord a => Lens' s a -> [s] -> [[s]]
sortsDesc _ [] = []
sortsDesc o xs = Map.elems $ Map.fromListWith (flip (++))
  [(Down (view o s), [s]) | s <- xs]

-- | Group a list through a lens.
groups :: Ord a => Lens' s a -> [s] -> [[s]]
groups = sorts

-- | Deduplicate a list through a lens, keeping first per group.
nubs :: Ord a => Lens' s a -> [s] -> [s]
nubs _ [] = []
nubs o xs = map head $ sorts o xs

---------------------------------------------------------------------
-- Container construction (List)
---------------------------------------------------------------------

-- | Build a 'Map.Map' keyed by lens focus from a list.
toMapOf :: Ord a => Lens' s a -> [s] -> Map.Map a [s]
toMapOf _ [] = Map.empty
toMapOf o xs = Map.fromListWith (flip (++)) [(view o s, [s]) | s <- xs]

-- | Count occurrences per key from a list.
countsOf :: Ord a => Lens' s a -> [s] -> Map.Map a Int
countsOf _ [] = Map.empty
countsOf o xs = Map.fromListWith (+) [(view o s, 1 :: Int) | s <- xs]

---------------------------------------------------------------------
-- Post-sort foldMapOf (List)
---------------------------------------------------------------------

-- | Sort through a lens, then right-fold each group.
foldSorts :: Ord a => Lens' s a -> (s -> r -> r) -> r -> [s] -> [r]
foldSorts o g z xs = map (foldr g z) (sorts o xs)

-- | Sort through a lens, then reduce each non-empty group.
foldSorts1 :: Ord a => Lens' s a -> (s -> s -> s) -> [s] -> [s]
foldSorts1 o f xs = map (foldr1 f) (sorts o xs)

-- | Sort through a lens, then monoidal concat per group.
mconcatSorts :: (Ord a, Monoid m) => Lens' s a -> (s -> m) -> [s] -> [m]
mconcatSorts o g xs = map (foldMap g) (sorts o xs)

---------------------------------------------------------------------
-- String sort
---------------------------------------------------------------------

-- | Sort a 'String' by a key on each character.
sortingString :: Ord k => (Char -> k) -> String -> Map.Map k String
sortingString = sortingRep length (\s i -> s !! i) id

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

-- | Construct a 'WhenMatched' merge tactic from a Sort.
-- Uses @i = ()@ (one position per key).
sortedMatched :: Sort () k (x, y) z -> Merge.SimpleWhenMatched k x y z
sortedMatched (Sort h) = Merge.zipWithMatched $ \k x y ->
  h (const (k, (x, y)))

-- | Construct a 'WhenMissing' merge tactic from a Sort.
-- Uses @i = ()@ (one position per key).
sortedMissing :: Sort () k x y -> Merge.SimpleWhenMissing k x y
sortedMissing (Sort h) = Merge.mapMissing $ \k x ->
  h (const (k, x))

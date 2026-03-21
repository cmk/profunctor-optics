{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
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
) where

import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Import
import Prelude (Int, Ord, Bounded, Enum, Eq, seq,
                (-), head, map, fst, snd, (.), ($), flip, fmap)

import qualified Data.Map.Strict as Map

---------------------------------------------------------------------
-- Sort carriers (Ord, Map)
---------------------------------------------------------------------

-- | Identity carrier for finite index types.
-- Groups by key, producing a 'Map' of lists.
mkSort :: (Bounded i, Enum i, Ord k) => Sort i k a (Map.Map k [a])
mkSort = Sort $ \inp ->
  Map.fromListWith (flip (++)) [ ki `seq` a `seq` (ki, [a])
                                | i <- [minBound..maxBound]
                                , let (ki, a) = inp i ]

-- | Identity carrier for Int-indexed containers of known size.
--
-- /Benchmark: 0.90–0.99x vs direct Map.fromListWith (zero-cost). See "Data.Profunctor.Optic.Bench"./
--
mkSortN :: Ord k => Int -> Sort Int k a (Map.Map k [a])
mkSortN n = Sort $ \inp ->
  Map.fromListWith (flip (++)) [ ki `seq` a `seq` (ki, [a])
                                | i <- [0..n-1]
                                , let (ki, a) = inp i ]

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

-- | Sort + deduplicate: keep first element per key.
sortUniqueRep :: Ord k
              => (c -> Int) -> (c -> Int -> a) -> (a -> c')
              -> (a -> k) -> c -> Map.Map k c'
sortUniqueRep len idx build key c =
  fmap (build . head) $ sortingRep len idx id key c

-- | Tagged sort: sort keys + permute values in tandem.
sortTaggedRep :: Ord k
              => (ck -> Int) -> (ck -> Int -> k) -> (cv -> Int -> v)
              -> ([k] -> ck') -> ([v] -> cv')
              -> ck -> cv -> Map.Map k (ck', cv')
sortTaggedRep klen kidx vidx kbuild vbuild ks vs =
  let n = klen ks
      result = runSort (mkSortN n) (\i -> (kidx ks i, (kidx ks i, vidx vs i)))
  in  fmap (\pairs -> (kbuild (map fst pairs), vbuild (map snd pairs))) result

-- | Group by key, returning Map from keys to value containers.
groupTaggedRep :: Ord k
               => (ck -> Int) -> (ck -> Int -> k) -> (cv -> Int -> v)
               -> ([v] -> cv') -> ck -> cv -> Map.Map k cv'
groupTaggedRep klen kidx vidx vbuild ks vs =
  let n = klen ks
      result = runSort (mkSortN n) (\i -> (kidx ks i, vidx vs i))
  in  fmap vbuild result

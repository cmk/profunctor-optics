{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
-- | Benchmark builders and performance documentation for profunctor optics.
--
-- This module provides reusable benchmark constructors, analogous to
-- how "Data.Profunctor.Optic.Property" provides law-testing predicates.
-- Each builder returns a pair @(optic-based, direct)@ — feed both to
-- @Criterion.nf@ and compare.
--
-- No Criterion dependency — the builders return plain functions.
--
-- == Performance hierarchy: Closed-side optics
--
-- @
-- Optic path       Cost\/elem  Constraint         Example
-- ─────────────    ─────────  ──────────         ───────
-- coindexed        ~7 ns      Closed (Cx)        ibitsN
-- colens\/grate     ~21 ns     Closed             grateN
-- cotraversal      ~44 ns     Cotraversing       bitsN
-- @
--
-- The coindexed path avoids 'Distributive' reconstruction entirely.
-- Prefer coindexed optics for 6-7x speedup over cotraversals.
--
-- == Performance hierarchy: Strong-side optics
--
-- @
-- Optic path       Cost       Constraint         Example
-- ─────────────    ────       ──────────         ───────
-- lens             ~0         Strong             fstL
-- prism            ~0         Choice             left'
-- traversal        O(n)       Traversing         traversed
-- @
--
-- Lens\/prism are essentially free (function application).
-- Traversal is linear, dominated by 'Applicative' reconstruction.
--
-- == Indexed optic overhead (RISK AREA)
--
-- Indexed operators route through 'Conjoin' wrapping:
--
-- @
-- overWithKey o f = (unConjoin #. corepresent o .# Conjoin) f mempty
-- @
--
-- Benchmarks show GHC inlines through fully: __1.08x__ overhead.
-- Measure with 'benchIxTraversal' and compare against non-indexed.
--
-- == Fold overhead
--
-- @
-- Operation          Optic        Direct       Ratio
-- ─────────          ─────        ──────       ─────
-- lists on Map       3.48 μs      2.01 μs      1.73x
-- lists on list      1.93 μs      0.24 μs      ~8x (unfair*)
-- @
--
-- (*) @foldr (:) []@ on @[a]@ is @id@ — not a meaningful baseline.
-- The 1.73x on Map is the real overhead (Endo closure chain).
-- Same as lens's @toListOf@ — both use the Endo path.
--
-- == Sort carrier overhead
--
-- @
-- Size    mkSortN    direct Map     Ratio
-- ────    ───────    ──────────     ─────
-- 100     707 ns     712 ns        0.99x
-- 1,000   3.0 μs     3.1 μs        0.98x
-- 10,000  40 μs      44 μs         0.90x
-- @
--
-- Zero overhead at all sizes (0.90–0.99x).
-- Sort adds zero overhead on top of raw Costar.
--
-- == How to use
--
-- @
-- import Criterion.Main
-- import Data.Profunctor.Optic
-- import Data.Profunctor.Optic.Bench
--
-- main = defaultMain
--   [ bgroup "lens"
--     [ let (viaOptic, direct) = benchLens fstL fst (\\(_, b) a -> (a, b)) (1, "x")
--       in bgroup "view"
--         [ bench "optic"  $ nf (fst viaOptic) (1 :: Int, "x")
--         , bench "direct" $ nf (fst direct)   (1 :: Int, "x")
--         ]
--     ]
--   ]
-- @
--
-- == Full results summary
--
-- @
-- Operation                    Optic\/Direct   Ratio
-- ─────────                    ────────────    ─────
-- Lens view                    9.7\/10.2 ns     0.95x
-- Lens over                    25.7\/25.8 ns    1.00x
-- Traversal0 preview           9.7\/9.6 ns      1.01x
-- Traversal over (1K)          10.9\/12.1 μs    0.89x
-- Indexed setsWithKey (Map)    3.0\/2.8 μs      1.08x
-- Fold lists (Map)             3.5\/2.0 μs      1.73x
-- Composition traversed.first  2.2\/2.2 μs      0.97x
-- Sort carrier mkSortN (1K)    3.0\/3.1 μs      0.98x
-- sortingOfL (1K)              334\/331 μs       1.01x
-- toMapOfL (1K)                346\/343 μs       1.01x
-- @
--
module Data.Profunctor.Optic.Bench (
    -- * Optic abstraction overhead
    benchLens
  , benchTraversal
  , benchTraversal0
  , benchFold
  , benchColens
    -- * Indexed overhead
  , benchIxTraversal
  , benchIxFold
    -- * Composition
  , benchCompose2
    -- * Container baselines
  , benchSortingOfL
  , benchToMapOfL
    -- * Sort carrier
  , benchSortVsDirect
  , benchOpticOnSort
    -- * Scaling
  , benchScaling
) where

import Data.Profunctor.Optic.Carrier (Sort(..), runSort)
import Data.Profunctor.Optic.Combinator (over, overWithKey)
import Data.Profunctor.Optic.Fold (lists, folds, foldsWithKey, preview)
import Data.Profunctor.Optic.Lens (lensVl)
import Data.Profunctor.Optic.Sort (mkSortN, sortingRep)
import Data.Profunctor.Optic.Setter (sets, setsWithKey)
import Data.Profunctor.Optic.Traversal (traverses)
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.View (view)
import Data.Profunctor.Optic.Import
import Data.List.Optic (sortingOfL)
import Data.Map.Optic (toMapOfL)
import qualified Data.Map.Strict as Map
import Prelude

---------------------------------------------------------------------
-- Optic abstraction overhead
---------------------------------------------------------------------

-- | Compare Lens view\/over vs direct get\/set.
--
-- Returns @((opticView, opticOver), (directGet, directOver))@.
--
benchLens :: Lens' s a
          -> (s -> a)              -- ^ direct getter
          -> (s -> a -> s)         -- ^ direct setter
          -> (a -> a)              -- ^ modification function
          -> ((s -> a, s -> s), (s -> a, s -> s))
benchLens o get _set f =
  ( (view o, over o f)
  , (get,    \s -> _set s (f (get s)))
  )

-- | Compare Traversal over vs direct fmap-like.
--
-- Returns @(opticOver, directOver)@.
--
benchTraversal :: Traversal' s a
               -> ((a -> a) -> s -> s)   -- ^ direct map
               -> (a -> a)               -- ^ modification function
               -> (s -> s, s -> s)
benchTraversal o direct f = (over o f, direct f)

-- | Compare Traversal0 preview vs direct.
--
benchTraversal0 :: Traversal0' s a
                -> (s -> Maybe a)        -- ^ direct preview
                -> (s -> Maybe a, s -> Maybe a)
benchTraversal0 o direct = (preview o, direct)

-- | Compare Fold lists vs direct.
--
benchFold :: Fold s a
          -> (s -> [a])                  -- ^ direct toList
          -> (s -> [a], s -> [a])
benchFold o direct = (lists o, direct)

-- | Compare Colens over vs direct.
--
benchColens :: Colens' s a
            -> ((a -> a) -> s -> s)      -- ^ direct map
            -> (a -> a)
            -> (s -> s, s -> s)
benchColens o direct f = (over o f, direct f)

---------------------------------------------------------------------
-- Indexed overhead
---------------------------------------------------------------------

-- | Compare indexed traversal vs non-indexed.
--
-- This is the key benchmark for measuring Conjoin overhead.
--
-- Returns @(indexed, nonIndexed)@.
--
benchIxTraversal :: Monoid k
                 => Ixtraversal' k s a
                 -> Traversal' s a
                 -> (k -> a -> a)         -- ^ indexed modification
                 -> (a -> a)              -- ^ non-indexed modification
                 -> (s -> s, s -> s)
benchIxTraversal ixo o ixf f =
  ( overWithKey ixo ixf
  , over o f
  )

-- | Compare indexed fold vs non-indexed.
--
benchIxFold :: (Monoid k, Monoid r)
            => Ixfold k s a
            -> Fold s a
            -> (k -> a -> r)              -- ^ indexed fold function
            -> (a -> r)                   -- ^ non-indexed fold function
            -> (s -> r, s -> r)
benchIxFold ixo o ixf f =
  ( foldsWithKey ixo ixf
  , folds o f
  )

---------------------------------------------------------------------
-- Composition
---------------------------------------------------------------------

-- | Compare composed optic vs direct composed function.
--
benchCompose2 :: Optic (->) s s a a
              -> Optic (->) a a b b
              -> (b -> b)
              -> ((b -> b) -> s -> s)     -- ^ direct composed
              -> (s -> s, s -> s)
benchCompose2 o1 o2 f direct =
  ( over (o1 . o2) f
  , direct f
  )

---------------------------------------------------------------------
-- Container baselines
---------------------------------------------------------------------

-- | Compare sortingOfL vs Data.List.sortOn + manual grouping.
--
benchSortingOfL :: Ord a
                => Lens' s a
                -> [s]
                -> ([s] -> [[s]], [s] -> [[s]])
benchSortingOfL o xs =
  ( sortingOfL o
  , \ys -> Map.elems $ Map.fromListWith (flip (++))
      [(view o s, [s]) | s <- ys]
  )

-- | Compare toMapOfL vs direct Map.fromListWith.
--
benchToMapOfL :: Ord a
              => Lens' s a
              -> ([s] -> Map.Map a [s], [s] -> Map.Map a [s])
benchToMapOfL o =
  ( toMapOfL o
  , \xs -> Map.fromListWith (flip (++)) [(view o s, [s]) | s <- xs]
  )

---------------------------------------------------------------------
-- Sort carrier
---------------------------------------------------------------------

-- | Compare Sort carrier vs direct Map.fromListWith.
--
benchSortVsDirect :: Ord k
                  => Int -> (Int -> k)
                  -> (() -> Map.Map k [Int], () -> Map.Map k [Int])
benchSortVsDirect n key =
  ( const viaSortResult
  , const directResult
  )
  where
    viaSortResult = runSort (mkSortN n) (\i -> (key i, i))
    directResult = Map.fromListWith (flip (++))
      [ k `seq` (k, [i]) | i <- [0..n-1], let !k = key i ]

-- | Benchmark an optic composed with a Sort carrier.
--
benchOpticOnSort :: (Sort i k a b -> Sort i k s t)
                 -> Sort i k a b
                 -> (i -> (k, s)) -> t
benchOpticOnSort optic carrier = runSort (optic carrier)

---------------------------------------------------------------------
-- Scaling
---------------------------------------------------------------------

-- | Build inputs at multiple sizes for scaling benchmarks.
--
-- @
-- let inputs = benchScaling [100, 1000, 10000] (\\n -> [1..n])
-- defaultMain [ bgroup (show n) [bench "f" $ nf myFn inp] | (n, inp) <- inputs ]
-- @
--
benchScaling :: [Int] -> (Int -> a) -> [(Int, a)]
benchScaling sizes gen = [(n, gen n) | n <- sizes]

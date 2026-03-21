{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
-- | Benchmark builders and performance documentation for profunctor optics.
--
-- This module provides reusable functions for measuring optic
-- performance, analogous to how "Data.Profunctor.Optic.Property"
-- provides reusable predicates for law-testing.
--
-- Import into your @bench\/Main.hs@ alongside @Criterion@ to build
-- benchmarks for your own optics.
--
-- == Performance hierarchy for Closed-side optics
--
-- When composing optics with 'Sort' or 'Costar'-shaped carriers,
-- the optic path determines the constant-factor overhead:
--
-- @
-- Optic path       Cost\/elem  Constraint         Example
-- ─────────────    ─────────  ──────────         ───────
-- coindexed        ~7 ns      Closed (Cx)        ibitsN
-- colens\/grate     ~21 ns     Closed             grateN
-- cotraversal      ~44 ns     Cotraversing       bitsN
-- @
--
-- The coindexed path (via 'Cxlens') avoids the 'Distributive'
-- overhead entirely. Prefer coindexed optics for 6-7x speedup
-- over cotraversals.
--
-- The carrier itself ('Sort', 'Costar') adds __zero__ overhead —
-- the cost is entirely from the optic. Benchmarks confirm:
--
-- @
-- Benchmark              Sort carrier    raw Costar    Ratio
-- ─────────              ────────────    ──────────    ─────
-- grate8                 167 ns          167 ns        1.00x
-- bits8                  1072 ns         1000 ns       1.07x
-- ibits8                 12 ns           —             ~bare
-- @
--
-- == Sort carrier overhead
--
-- @
-- Size    mkSortN    direct Map     Ratio
-- ────    ───────    ──────────     ─────
-- 100     15 μs      8.5 μs        1.8x
-- 1,000   213 μs     131 μs        1.6x
-- 10,000  21.2 ms    21.2 ms       1.0x
-- @
--
-- Constant-factor overhead at small sizes, converges to 1.0x.
-- Dominated by @Map.fromListWith@ at scale.
--
-- == Pipeline overhead
--
-- The '%.' composition operator adds __zero__ overhead.
-- Single-pass and two-pass benchmarks are identical within
-- measurement noise.
module Data.Profunctor.Optic.Bench (
    -- * Sort carrier comparison
    benchSortVsDirect
    -- * Optic composition comparison
  , benchOpticOnSort
) where

import Data.Profunctor.Optic.Carrier (Sort(..), runSort)
import Data.Profunctor.Optic.Sort (mkSortN)
import qualified Data.Map.Strict as Map
import Prelude

-- | Build a pair of functions for benchmarking 'Sort' carrier
-- overhead against direct @Map.fromListWith@.
--
-- @
-- import Criterion.Main
--
-- main = defaultMain
--   [ bgroup "carrier"
--     [ bench "mkSortN"  $ nf (fst $ benchSortVsDirect 1000 (`mod` 50)) ()
--     , bench "direct"   $ nf (snd $ benchSortVsDirect 1000 (`mod` 50)) ()
--     ]
--   ]
-- @
--
benchSortVsDirect :: Ord k
                  => Int          -- ^ number of elements
                  -> (Int -> k)   -- ^ key extractor
                  -> (() -> Map.Map k [Int], () -> Map.Map k [Int])
benchSortVsDirect n key =
  ( const viaSortResult
  , const directResult
  )
  where
    viaSortResult = runSort (mkSortN n) (\i -> (key i, i))
    directResult = Map.fromListWith (flip (++))
      [ k `seq` (k, [i]) | i <- [0..n-1], let !k = key i ]

-- | Benchmark an optic composed with a 'Sort' carrier.
--
-- Returns a function that runs the optic-lifted carrier on
-- the given input. Compare against a bare carrier to measure
-- optic overhead.
--
-- @
-- let lifted = benchOpticOnSort grate8 baseCarrier
-- bench "grate8+Sort" $ nf lifted inp
-- @
--
benchOpticOnSort :: (Sort i k a b -> Sort i k s t)
                 -> Sort i k a b
                 -> (i -> (k, s)) -> t
benchOpticOnSort optic carrier = runSort (optic carrier)

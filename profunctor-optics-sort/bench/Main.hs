{-# LANGUAGE BangPatterns #-}

-- | Focused pre-merge benchmarks for SortF.
--
-- Three questions:
-- 1. Carrier overhead: mkSortFN vs hand-written Map.fromListWith
-- 2. Optic composition: grate8 carrier vs bare carrier
-- 3. INLINE effectiveness: does DerivingVia specialize?
module Main (main) where

import Criterion.Main
import Data.Functor.Compose (Compose(..))
import Data.Functor.Index (I8(..))
import Data.Monoid (Sum(..))
import Data.Profunctor.Sort
import Data.Profunctor.Types (Costar(..))
import Data.Word (Word8)
import Data.Word.Optic (grate8, bits8, ibits8)
import qualified Data.Map.Strict as Map

main :: IO ()
main = defaultMain
  [ carrierOverhead
  , opticComposition
  , pipelineOverhead
  ]

---------------------------------------------------------------------
-- 1. Carrier overhead: mkSortFN vs hand-written Map.fromListWith
---------------------------------------------------------------------

carrierOverhead :: Benchmark
carrierOverhead = bgroup "carrier-overhead"
  [ bgroup (show n)
    [ bench "mkSortFN"   $ nf (viaSortF n) keyFn
    , bench "direct-Map" $ nf (directMap n) keyFn
    ]
  | n <- [100, 1000, 10000]
  ]
  where
    keyFn :: Int -> Int
    keyFn i = i `mod` 50

-- SortF carrier: mkSortFN + runSortF
viaSortF :: Int -> (Int -> Int) -> Map.Map Int [Int]
viaSortF n key = runSortF (mkSortFN n) (\i -> (key i, i))

-- Hand-written: same logic, no SortF wrapper
directMap :: Int -> (Int -> Int) -> Map.Map Int [Int]
directMap n key =
  Map.fromListWith (flip (++)) [ k `seq` (k, [i])
                                | i <- [0..n-1]
                                , let !k = key i ]

---------------------------------------------------------------------
-- 2. Optic composition: grate8 carrier vs bare carrier
---------------------------------------------------------------------

opticComposition :: Benchmark
opticComposition = bgroup "optic-composition"
  [ bench "bare-carrier"         $ nf bareCarrier      inputW8
  , bench "grate8-SortF"         $ nf grate8SortF      inputW8
  , bench "grate8-Costar"        $ nf grate8Costar     inputCostar
  , bench "bits8-SortF"          $ nf bits8SortF       inputW8
  , bench "bits8-Costar"         $ nf bits8Costar      inputCostar
  , bench "ibits8-SortF"         $ nf ibits8SortF      inputW8
  , bench "bare-Int-idx"        $ nf bareCarrierInt   inputInt
  , bench "grate8-Int-idx"      $ nf grate8IntIdx     inputInt
  ]
  where
    inputW8 :: I8 -> (Int, Word8)
    inputW8 _ = (0, 42)

    inputInt :: Int -> (Int, Word8)
    inputInt _ = (0, 42)

    inputCostar :: Compose ((->) I8) ((,) Int) Word8
    inputCostar = Compose $ \_ -> (0, 42)

-- Bare SortF carrier: trivial (one function call)
bareCarrier :: (I8 -> (Int, Word8)) -> Word8
bareCarrier = runSortF baseSortF
  where
    baseSortF :: SortF I8 Int Word8 Word8
    baseSortF = SortF $ \inp -> snd (inp I81)

-- grate8 applied to SortF
grate8SortF :: (I8 -> (Int, Word8)) -> Word8
grate8SortF = runSortF liftedSortF
  where
    baseSortF :: SortF I8 Int (I8 -> Bool) (I8 -> Bool)
    baseSortF = SortF $ \inp -> snd (inp I81)
    liftedSortF :: SortF I8 Int Word8 Word8
    liftedSortF = grate8 baseSortF

-- grate8 applied to raw Costar (same Corep functor, no SortF)
grate8Costar :: Compose ((->) I8) ((,) Int) Word8 -> Word8
grate8Costar = runCostar liftedCostar
  where
    baseCostar :: Costar (Compose ((->) I8) ((,) Int)) (I8 -> Bool) (I8 -> Bool)
    baseCostar = Costar $ \(Compose inp) -> snd (inp I81)
    liftedCostar :: Costar (Compose ((->) I8) ((,) Int)) Word8 Word8
    liftedCostar = grate8 baseCostar

-- bits8 applied to SortF
bits8SortF :: (I8 -> (Int, Word8)) -> Word8
bits8SortF = runSortF liftedSortF
  where
    baseSortF :: SortF I8 Int Bool Bool
    baseSortF = SortF $ \inp -> snd (inp I81)
    liftedSortF :: SortF I8 Int Word8 Word8
    liftedSortF = bits8 baseSortF

-- bits8 applied to raw Costar (same Corep functor, no SortF)
bits8Costar :: Compose ((->) I8) ((,) Int) Word8 -> Word8
bits8Costar = runCostar liftedCostar
  where
    baseCostar :: Costar (Compose ((->) I8) ((,) Int)) Bool Bool
    baseCostar = Costar $ \(Compose inp) -> snd (inp I81)
    liftedCostar :: Costar (Compose ((->) I8) ((,) Int)) Word8 Word8
    liftedCostar = bits8 baseCostar

-- ibits8 (cxlens, coindexed) — should be 6-7x faster than bits8
ibits8SortF :: (I8 -> (Int, Word8)) -> (I8 -> Word8)
ibits8SortF = runSortF liftedSortF
  where
    -- Carrier output is (I8 -> Bool) for the Cx wrapping
    baseSortF :: SortF I8 Int Bool (I8 -> Bool)
    baseSortF = SortF $ \inp -> const (snd (inp I81))
    liftedSortF :: SortF I8 Int Word8 (I8 -> Word8)
    liftedSortF = ibits8 baseSortF

-- Same as bare but with Int index instead of I8
bareCarrierInt :: (Int -> (Int, Word8)) -> Word8
bareCarrierInt = runSortF baseSortF
  where
    baseSortF :: SortF Int Int Word8 Word8
    baseSortF = SortF $ \inp -> snd (inp 0)

-- grate8 with Int-indexed SortF (Int is Monoid via Sum, but we just
-- need Closed here so Int works directly)
grate8IntIdx :: (Int -> (Int, Word8)) -> Word8
grate8IntIdx = runSortF liftedSortF
  where
    baseSortF :: SortF Int Int (I8 -> Bool) (I8 -> Bool)
    baseSortF = SortF $ \inp -> snd (inp 0)
    liftedSortF :: SortF Int Int Word8 Word8
    liftedSortF = grate8 baseSortF

---------------------------------------------------------------------
-- 3. Pipeline overhead: (%.) composition vs single pass
---------------------------------------------------------------------

pipelineOverhead :: Benchmark
pipelineOverhead = bgroup "pipeline"
  [ bgroup (show n)
    [ bench "single-pass" $ nf (singlePass n) keyFn
    , bench "two-pass"    $ nf (twoPass n)    keyFn
    ]
  | n <- [100, 1000, 10000]
  ]
  where
    keyFn :: Int -> Int
    keyFn i = i `mod` 50

-- Single SortF pass
singlePass :: Int -> (Int -> Int) -> Map.Map Int [Int]
singlePass n key = runSortF (mkSortFN n) (\i -> (key i, i))

-- Two passes chained with (%.)
-- First pass: extract the value. Second pass: build the Map.
-- The (%.) pipelines g's output as f's input value.
twoPass :: Int -> (Int -> Int) -> Map.Map Int [Int]
twoPass n key = runSortF (mkSortFN n %. extractSortF) (\i -> (key i, i))
  where
    -- First stage: extract the value at each position (identity on values)
    extractSortF :: SortF Int Int Int Int
    extractSortF = SortF $ \inp -> snd (inp 0)

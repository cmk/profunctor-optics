{-# LANGUAGE TemplateHaskell #-}

module Test.Prop.Container (tests) where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Data.Container.Pattern
import Data.Map.Optic (depth, sizes, rebalanced)
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import qualified Data.Set as Set
import qualified Data.IntSet as IntSet

tests :: IO Bool
tests = checkParallel $$(discover)

---------------------------------------------------------------------
-- Map round-trips
---------------------------------------------------------------------

prop_map_roundtrip :: Property
prop_map_roundtrip = property $ do
    kvs <- forAll $ Gen.list (Range.linear 0 50)
        ((,) <$> Gen.int (Range.linear 0 100) <*> Gen.string (Range.linear 0 10) Gen.alpha)
    let m = Map.fromList kvs
    fromMapF (toMapF m) === m

prop_map_depth_positive :: Property
prop_map_depth_positive = property $ do
    kvs <- forAll $ Gen.list (Range.linear 1 50)
        ((,) <$> Gen.int (Range.linear 0 100) <*> Gen.int (Range.linear 0 100))
    let m = Map.fromList kvs
    assert $ depth m >= 1

prop_map_depth_empty :: Property
prop_map_depth_empty = property $ do
    depth (Map.empty :: Map.Map Int Int) === 0

prop_map_sizes_sum :: Property
prop_map_sizes_sum = property $ do
    kvs <- forAll $ Gen.list (Range.linear 0 50)
        ((,) <$> Gen.int (Range.linear 0 100) <*> Gen.int (Range.linear 0 100))
    let m = Map.fromList kvs
    -- Root size equals map size
    case sizes m of
        [] -> Map.size m === 0
        (s : _) -> s === Map.size m

prop_map_rebalanced :: Property
prop_map_rebalanced = property $ do
    kvs <- forAll $ Gen.list (Range.linear 0 50)
        ((,) <$> Gen.int (Range.linear 0 100) <*> Gen.int (Range.linear 0 100))
    let m = Map.fromList kvs
    rebalanced m === m

---------------------------------------------------------------------
-- IntMap round-trips
---------------------------------------------------------------------

prop_intmap_roundtrip :: Property
prop_intmap_roundtrip = property $ do
    kvs <- forAll $ Gen.list (Range.linear 0 50)
        ((,) <$> Gen.int (Range.linear 0 100) <*> Gen.string (Range.linear 0 10) Gen.alpha)
    let m = IntMap.fromList kvs
    fromIntMapF (toIntMapF m) === m

---------------------------------------------------------------------
-- Set round-trips
---------------------------------------------------------------------

prop_set_roundtrip :: Property
prop_set_roundtrip = property $ do
    xs <- forAll $ Gen.list (Range.linear 0 50) (Gen.int (Range.linear 0 100))
    let s = Set.fromList xs
    fromSetF (toSetF s) === s

---------------------------------------------------------------------
-- IntSet round-trips
---------------------------------------------------------------------

prop_intset_roundtrip :: Property
prop_intset_roundtrip = property $ do
    xs <- forAll $ Gen.list (Range.linear 0 50) (Gen.int (Range.linear 0 100))
    let s = IntSet.fromList xs
    fromIntSetF (toIntSetF s) === s

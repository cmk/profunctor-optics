{-# LANGUAGE TemplateHaskell #-}

module Test.Data.List.Optic (tests) where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Data.List (sort, nub)
import Data.List.Optic
import Data.Profunctor.Optic

tests :: IO Bool
tests = checkParallel $$(discover)

-- at: access element at valid index
prop_at_get :: Property
prop_at_get = property $ do
    xs <- forAll $ Gen.list (Range.linear 1 10) (Gen.int (Range.linear 0 100))
    i <- forAll $ Gen.int (Range.linear 0 (length xs - 1))
    preview (at i) xs === Just (xs !! i)

-- at: missing index returns Nothing
prop_at_missing :: Property
prop_at_missing = property $ do
    xs <- forAll $ Gen.list (Range.linear 0 5) (Gen.int (Range.linear 0 100))
    preview (at (length xs + 1)) xs === Nothing

-- at: negative index returns Nothing
prop_at_negative :: Property
prop_at_negative = property $ do
    xs <- forAll $ Gen.list (Range.linear 0 5) (Gen.int (Range.linear 0 100))
    preview (at (-1)) xs === Nothing

-- at: set then get roundtrip
prop_at_set_get :: Property
prop_at_set_get = property $ do
    xs <- forAll $ Gen.list (Range.linear 1 10) (Gen.int (Range.linear 0 100))
    i <- forAll $ Gen.int (Range.linear 0 (length xs - 1))
    v <- forAll $ Gen.int (Range.linear 0 100)
    preview (at i) (set (at i) v xs) === Just v

-- at: set preserves length
prop_at_set_length :: Property
prop_at_set_length = property $ do
    xs <- forAll $ Gen.list (Range.linear 1 10) (Gen.int (Range.linear 0 100))
    i <- forAll $ Gen.int (Range.linear 0 (length xs - 1))
    v <- forAll $ Gen.int (Range.linear 0 100)
    length (set (at i) v xs) === length xs

---------------------------------------------------------------------
-- *By operators
---------------------------------------------------------------------

-- groupSortBy: groups equal elements
prop_groupSortBy_groups :: Property
prop_groupSortBy_groups = property $ do
    xs <- forAll $ Gen.list (Range.linear 0 20) (Gen.int (Range.linear 0 5))
    let result = groupSortBy compare (:) xs
    -- All elements preserved
    sum (map length result) === length xs

-- groupSortBy: output is sorted
prop_groupSortBy_sorted :: Property
prop_groupSortBy_sorted = property $ do
    xs <- forAll $ Gen.list (Range.linear 0 20) (Gen.int (Range.linear 0 10))
    let result = groupSortBy compare (\h t -> h : t) xs
        heads = map head result
    heads === sort (nub xs)

-- uniqueSort: no duplicates
prop_uniqueSort :: Property
prop_uniqueSort = property $ do
    xs <- forAll $ Gen.list (Range.linear 0 20) (Gen.int (Range.linear 0 10))
    let result = uniqueSort xs
    result === nub (sort xs)

-- uniqueSortOn: dedup by projection
prop_uniqueSortOn :: Property
prop_uniqueSortOn = property $ do
    xs <- forAll $ Gen.list (Range.linear 0 20) (Gen.int (Range.linear 0 10))
    let result = uniqueSortOn id xs
    result === uniqueSort xs

-- groupSortOn: groups by key
prop_groupSortOn :: Property
prop_groupSortOn = property $ do
    let xs = [(2, "b"), (1, "a"), (2, "c"), (1, "d")]
        result = groupSortOn fst (\_ x rest -> snd x : map snd rest) xs
    result === [["a", "d"], ["b", "c"]]

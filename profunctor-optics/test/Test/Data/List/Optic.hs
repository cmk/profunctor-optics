{-# LANGUAGE TemplateHaskell #-}

module Test.Data.List.Optic (tests) where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

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

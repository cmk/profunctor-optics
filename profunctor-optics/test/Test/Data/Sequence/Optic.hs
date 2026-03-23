{-# LANGUAGE TemplateHaskell #-}

module Test.Data.Sequence.Optic (tests) where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Data.Sequence.Optic
import Data.Profunctor.Optic
import qualified Data.Sequence as Seq

tests :: IO Bool
tests = checkParallel $$(discover)

-- slicedTo: first n elements
prop_slicedTo_length :: Property
prop_slicedTo_length = property $ do
    xs <- forAll $ Gen.list (Range.linear 0 20) (Gen.int (Range.linear 0 100))
    n <- forAll $ Gen.int (Range.linear 0 (length xs + 5))
    let s = Seq.fromList xs
        result = s ^.. slicedTo n
    length result === min n (Seq.length s)

-- slicedFrom: all but first n
prop_slicedFrom_length :: Property
prop_slicedFrom_length = property $ do
    xs <- forAll $ Gen.list (Range.linear 0 20) (Gen.int (Range.linear 0 100))
    n <- forAll $ Gen.int (Range.linear 0 (length xs + 5))
    let s = Seq.fromList xs
        result = s ^.. slicedFrom n
    length result === max 0 (Seq.length s - n)

-- sliced: range [i, j)
prop_sliced_range :: Property
prop_sliced_range = property $ do
    xs <- forAll $ Gen.list (Range.linear 0 20) (Gen.int (Range.linear 0 100))
    let n = length xs
    i <- forAll $ Gen.int (Range.linear 0 n)
    j <- forAll $ Gen.int (Range.linear i n)
    let s = Seq.fromList xs
        result = s ^.. sliced i j
    length result === (j - i)

-- viewedl: iso roundtrip
prop_viewedl_roundtrip :: Property
prop_viewedl_roundtrip = property $ do
    xs <- forAll $ Gen.list (Range.linear 0 20) (Gen.int (Range.linear 0 100))
    let s = Seq.fromList xs
    coview viewedl (view viewedl s) === s

-- viewedr: iso roundtrip
prop_viewedr_roundtrip :: Property
prop_viewedr_roundtrip = property $ do
    xs <- forAll $ Gen.list (Range.linear 0 20) (Gen.int (Range.linear 0 100))
    let s = Seq.fromList xs
    coview viewedr (view viewedr s) === s

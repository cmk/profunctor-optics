{-# LANGUAGE TemplateHaskell #-}

module Test.Data.IntSet.Optic (tests) where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Data.IntSet.Optic as ISO
import Data.Profunctor.Optic hiding (folded)
import qualified Data.IntSet as IS

tests :: IO Bool
tests = checkParallel $$(discover)

genIntSet :: Gen IS.IntSet
genIntSet = IS.fromList <$> Gen.list (Range.linear 0 20) (Gen.int (Range.linear 0 50))

-- folded collectOf all elements
prop_folded_count :: Property
prop_folded_count = property $ do
    s <- forAll genIntSet
    length (s ^.. folded) === IS.size s

-- folded elements are ascending
prop_folded_ascending :: Property
prop_folded_ascending = property $ do
    s <- forAll genIntSet
    let xs = s ^.. folded
    xs === IS.toAscList s

-- listed roundtrip
prop_listed_roundtrip :: Property
prop_listed_roundtrip = property $ do
    s <- forAll genIntSet
    coview listed (view listed s) === s

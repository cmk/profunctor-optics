{-# LANGUAGE TemplateHaskell #-}

module Test.Data.Set.Optic (tests) where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Data.Set.Optic as SO
import Data.Profunctor.Optic hiding (folded)
import qualified Data.Set as Set

tests :: IO Bool
tests = checkParallel $$(discover)

genSet :: Gen (Set.Set Int)
genSet = Set.fromList <$> Gen.list (Range.linear 0 20) (Gen.int (Range.linear 0 50))

-- folded collectOf all elements
prop_folded_count :: Property
prop_folded_count = property $ do
    s <- forAll genSet
    length (s ^.. folded) === Set.size s

-- folded elements are ascending
prop_folded_ascending :: Property
prop_folded_ascending = property $ do
    s <- forAll genSet
    let xs = s ^.. folded
    xs === Set.toAscList s

-- listed roundtrip
prop_listed_roundtrip :: Property
prop_listed_roundtrip = property $ do
    s <- forAll genSet
    review listed (view listed s) === s

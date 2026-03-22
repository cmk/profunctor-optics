{-# LANGUAGE TemplateHaskell #-}

module Test.Data.Map.Optic (tests) where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Data.Map.Optic
import Data.Profunctor.Optic
import qualified Data.Map as Map

tests :: IO Bool
tests = checkParallel $$(discover)

genMap :: Gen (Map.Map Int String)
genMap = Map.fromList <$> Gen.list (Range.linear 1 20)
    ((,) <$> Gen.int (Range.linear 0 50) <*> Gen.string (Range.linear 1 5) Gen.alpha)

-- at: get existing key
prop_at_get :: Property
prop_at_get = property $ do
    m <- forAll genMap
    k <- forAll $ Gen.element (Map.keys m)
    preview (at k) m === Just (m Map.! k)

-- at: missing key
prop_at_missing :: Property
prop_at_missing = property $ do
    m <- forAll genMap
    let k = 999
    preview (at k) m === Nothing

-- at: set then get (on existing key)
prop_at_set_get :: Property
prop_at_set_get = property $ do
    m <- forAll genMap
    k <- forAll $ Gen.element (Map.keys m)
    v <- forAll $ Gen.string (Range.linear 1 5) Gen.alpha
    preview (at k) (set (at k) v m) === Just v

-- values: fold collectOf all values
prop_values_count :: Property
prop_values_count = property $ do
    m <- forAll genMap
    length (m ^.. values) === Map.size m

-- validated: valid maps pass
prop_validated_valid :: Property
prop_validated_valid = property $ do
    m <- forAll genMap
    case preview validated m of
        Just _  -> success
        Nothing -> failure

-- altered: insert via alter
prop_altered_insert :: Property
prop_altered_insert = property $ do
    m <- forAll genMap
    k <- forAll $ Gen.int (Range.linear 0 50)
    v <- forAll $ Gen.string (Range.linear 1 5) Gen.alpha
    over (altered k) (const (Just v)) m === Map.insert k v m

-- alteredF: lens roundtrip
prop_alteredF_roundtrip :: Property
prop_alteredF_roundtrip = property $ do
    m <- forAll genMap
    k <- forAll $ Gen.int (Range.linear 0 50)
    let v = view (alteredF k) m
    set (alteredF k) v m === m

-- cxmapped: coindexed cofold over map-of-maps
prop_cxmapped_cofold :: Property
prop_cxmapped_cofold = property $ do
    let nested = Map.fromList [("a", Map.fromList [("x", 1 :: Int), ("y", 2)])]
        result = cxfolds (cxmapped # cxmapped)
                   (\k r a -> Map.singleton k (a + r))
                   (0 :: Int)
                   nested
    -- The outer key "a" and inner keys "x","y" accumulate via (<>)
    -- result should be a nested map with combined keys
    assert $ not (Map.null result)

-- cxmapped: single-level cofold
prop_cxmapped_single :: Property
prop_cxmapped_single = property $ do
    let m = Map.fromList [("a", 1 :: Int), ("b", 2)]
        result = cxfolds cxmapped
                   (\k _r a -> Map.singleton k a)
                   (0 :: Int)
                   m
    Map.keys result === ["a", "b"]

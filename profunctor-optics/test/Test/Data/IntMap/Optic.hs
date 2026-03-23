{-# LANGUAGE TemplateHaskell #-}

module Test.Data.IntMap.Optic (tests) where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Data.IntMap.Optic
import Data.Profunctor.Optic
import Data.Profunctor.Optic.Lens (lensVl)
import Data.Profunctor.Optic.Types (Lens')
import qualified Data.IntMap.Strict as IM

tests :: IO Bool
tests = checkParallel $$(discover)

fstL :: Lens' (Int, String) Int
fstL = lensVl $ \f (a, b) -> (\a' -> (a', b)) <$> f a

genIntMap :: Gen (IM.IntMap String)
genIntMap = IM.fromList <$> Gen.list (Range.linear 1 20)
    ((,) <$> Gen.int (Range.linear 0 50) <*> Gen.string (Range.linear 1 5) Gen.alpha)

-- at: get existing key
prop_at_get :: Property
prop_at_get = property $ do
    m <- forAll genIntMap
    k <- forAll $ Gen.element (IM.keys m)
    preview (at k) m === IM.lookup k m

-- at: set then get
prop_at_set_get :: Property
prop_at_set_get = property $ do
    m <- forAll genIntMap
    k <- forAll $ Gen.element (IM.keys m)
    v <- forAll $ Gen.string (Range.linear 1 5) Gen.alpha
    preview (at k) (set (at k) v m) === Just v

-- values: count matchOf size
prop_values_count :: Property
prop_values_count = property $ do
    m <- forAll genIntMap
    length (m ^.. values) === IM.size m

-- toIntMapOfL: keys match
prop_toIntMapOfL_keys :: Property
prop_toIntMapOfL_keys = property $ do
    let xs = [(1, "a"), (2, "b"), (1, "c")] :: [(Int, String)]
        result = toIntMapOf fstL xs
    IM.keys result === [1, 2]

{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}

module Test.Prop.Text (tests) where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Encoding as TE
import Data.Text.Optic
import Data.Profunctor.Optic

tests :: IO Bool
tests = checkParallel $$(discover)

---------------------------------------------------------------------
-- lazy
---------------------------------------------------------------------

-- | view lazy . review lazy = id
prop_lazy_roundtrip :: Property
prop_lazy_roundtrip = property $ do
    s <- forAll $ Gen.text (Range.linear 0 100) Gen.unicode
    review lazy (view lazy s) === s

---------------------------------------------------------------------
-- packed
---------------------------------------------------------------------

-- | view packed . review packed = id
prop_packed_roundtrip :: Property
prop_packed_roundtrip = property $ do
    s <- forAll $ Gen.string (Range.linear 0 100) Gen.unicode
    review packed (view packed s) === s

-- | review packed . view packed = id
prop_packed_roundtrip_rev :: Property
prop_packed_roundtrip_rev = property $ do
    s <- forAll $ Gen.text (Range.linear 0 100) Gen.unicode
    view packed (review packed s) === s

---------------------------------------------------------------------
-- utf8
---------------------------------------------------------------------

-- | utf8 round-trips for valid text
prop_utf8_roundtrip :: Property
prop_utf8_roundtrip = property $ do
    s <- forAll $ Gen.text (Range.linear 0 100) Gen.unicode
    review utf8 (view utf8 s) === s

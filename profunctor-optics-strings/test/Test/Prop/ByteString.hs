{-# LANGUAGE TemplateHaskell #-}

module Test.Prop.ByteString (tests) where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Short as SBS
import Data.ByteString.Optic
import Data.Profunctor.Optic
import Data.Word (Word8)

tests :: IO Bool
tests = checkParallel $$(discover)

---------------------------------------------------------------------
-- short
---------------------------------------------------------------------

-- | view short . review short = id
prop_short_roundtrip :: Property
prop_short_roundtrip = property $ do
    ws <- forAll $ Gen.list (Range.linear 0 100) (Gen.word8 Range.linearBounded)
    let bs = BS.pack ws
    review short (view short bs) === bs

-- | review short . view short = id
prop_short_roundtrip_rev :: Property
prop_short_roundtrip_rev = property $ do
    ws <- forAll $ Gen.list (Range.linear 0 100) (Gen.word8 Range.linearBounded)
    let sbs = SBS.pack ws
    view short (review short sbs) === sbs

---------------------------------------------------------------------
-- lazy
---------------------------------------------------------------------

-- | view lazy . review lazy = id
prop_lazy_roundtrip :: Property
prop_lazy_roundtrip = property $ do
    ws <- forAll $ Gen.list (Range.linear 0 100) (Gen.word8 Range.linearBounded)
    let bs = BS.pack ws
    review lazy (view lazy bs) === bs

---------------------------------------------------------------------
-- packed
---------------------------------------------------------------------

-- | view packed . review packed = id
prop_packed_roundtrip :: Property
prop_packed_roundtrip = property $ do
    ws <- forAll $ Gen.list (Range.linear 0 100) (Gen.word8 Range.linearBounded)
    review packed (view packed ws) === ws

-- | review packed . view packed = id
prop_packed_roundtrip_rev :: Property
prop_packed_roundtrip_rev = property $ do
    ws <- forAll $ Gen.list (Range.linear 0 100) (Gen.word8 Range.linearBounded)
    let bs = BS.pack ws
    view packed (review packed bs) === bs

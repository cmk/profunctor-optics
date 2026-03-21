{-# LANGUAGE TemplateHaskell #-}

module Test.Prop.Word (tests) where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Control.Applicative (liftA2)
import Data.Bits (complement)
import Data.Functor.Index
import Data.Profunctor.Optic
import Data.Word.Optic
import Data.Word (Word8, Word16, Word32, Word64)

tests :: IO Bool
tests = checkParallel $$(discover)

---------------------------------------------------------------------
-- bits8
---------------------------------------------------------------------

-- | over bits8 id = id
prop_bits8_id :: Property
prop_bits8_id = property $ do
    w <- forAll $ Gen.word8 Range.linearBounded
    over bits8 id w === w

-- | over bits8 not = complement
prop_bits8_not :: Property
prop_bits8_not = property $ do
    w <- forAll $ Gen.word8 Range.linearBounded
    over bits8 not w === complement w

-- | over bits8 not . over bits8 not = id
prop_bits8_not_not :: Property
prop_bits8_not_not = property $ do
    w <- forAll $ Gen.word8 Range.linearBounded
    over bits8 not (over bits8 not w) === w

-- | toBits8 / fromBits8 round-trip
prop_bits8_roundtrip :: Property
prop_bits8_roundtrip = property $ do
    w <- forAll $ Gen.word8 Range.linearBounded
    fromBits8 (toBits8 w) === w

---------------------------------------------------------------------
-- bits16
---------------------------------------------------------------------

-- | over bits16 id = id
prop_bits16_id :: Property
prop_bits16_id = property $ do
    w <- forAll $ Gen.word16 Range.linearBounded
    over bits16 id w === w

-- | toBits16 / fromBits16 round-trip
prop_bits16_roundtrip :: Property
prop_bits16_roundtrip = property $ do
    w <- forAll $ Gen.word16 Range.linearBounded
    fromBits16 (toBits16 w) === w

---------------------------------------------------------------------
-- bits32
---------------------------------------------------------------------

-- | over bits32 id = id
prop_bits32_id :: Property
prop_bits32_id = property $ do
    w <- forAll $ Gen.word32 Range.linearBounded
    over bits32 id w === w

-- | toBits32 / fromBits32 round-trip
prop_bits32_roundtrip :: Property
prop_bits32_roundtrip = property $ do
    w <- forAll $ Gen.word32 Range.linearBounded
    fromBits32 (toBits32 w) === w

---------------------------------------------------------------------
-- bits64
---------------------------------------------------------------------

-- | over bits64 id = id
prop_bits64_id :: Property
prop_bits64_id = property $ do
    w <- forAll $ Gen.word64 Range.linearBounded
    over bits64 id w === w

-- | toBits64 / fromBits64 round-trip
prop_bits64_roundtrip :: Property
prop_bits64_roundtrip = property $ do
    w <- forAll $ Gen.word64 Range.linearBounded
    fromBits64 (toBits64 w) === w

---------------------------------------------------------------------
-- grate8
---------------------------------------------------------------------

-- | grate8 round-trips through bit representation
prop_grate8_id :: Property
prop_grate8_id = property $ do
    w <- forAll $ Gen.word8 Range.linearBounded
    over grate8 id w === w

---------------------------------------------------------------------
-- Indexed cotraversals
---------------------------------------------------------------------

-- | cxover ibits8 (const id) = id
prop_ibits8_id :: Property
prop_ibits8_id = property $ do
    w <- forAll $ Gen.word8 Range.linearBounded
    cxover ibits8 (const id) w === w

-- | cxover ibits8 (const not) = complement
prop_ibits8_not :: Property
prop_ibits8_not = property $ do
    w <- forAll $ Gen.word8 Range.linearBounded
    cxover ibits8 (const not) w === complement w

-- | cxover ibits16 (const id) = id
prop_ibits16_id :: Property
prop_ibits16_id = property $ do
    w <- forAll $ Gen.word16 Range.linearBounded
    cxover ibits16 (const id) w === w

-- | cxover ibits32 (const id) = id
prop_ibits32_id :: Property
prop_ibits32_id = property $ do
    w <- forAll $ Gen.word32 Range.linearBounded
    cxover ibits32 (const id) w === w

-- | cxover ibits64 (const id) = id
prop_ibits64_id :: Property
prop_ibits64_id = property $ do
    w <- forAll $ Gen.word64 Range.linearBounded
    cxover ibits64 (const id) w === w

---------------------------------------------------------------------
-- Grate zipping
---------------------------------------------------------------------

-- | zipsWith grate8 xor w w = 0
prop_grate8_xor_self :: Property
prop_grate8_xor_self = property $ do
    w <- forAll $ Gen.word8 Range.linearBounded
    zipsWith grate8 (liftA2 (/=)) w w === 0

-- | zipsWith grate16 xor w w = 0
prop_grate16_xor_self :: Property
prop_grate16_xor_self = property $ do
    w <- forAll $ Gen.word16 Range.linearBounded
    zipsWith grate16 (liftA2 (/=)) w w === 0

-- | zipsWith grate32 xor w w = 0
prop_grate32_xor_self :: Property
prop_grate32_xor_self = property $ do
    w <- forAll $ Gen.word32 Range.linearBounded
    zipsWith grate32 (liftA2 (/=)) w w === 0

-- | zipsWith grate64 xor w w = 0
prop_grate64_xor_self :: Property
prop_grate64_xor_self = property $ do
    w <- forAll $ Gen.word64 Range.linearBounded
    zipsWith grate64 (liftA2 (/=)) w w === 0

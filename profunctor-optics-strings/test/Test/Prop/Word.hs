{-# LANGUAGE TemplateHaskell #-}

module Test.Prop.Word (tests) where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

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

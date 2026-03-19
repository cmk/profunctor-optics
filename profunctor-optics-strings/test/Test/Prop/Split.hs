{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Test.Prop.Split (tests) where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as B8
import qualified Data.ByteString.Optic as BO
import Data.Profunctor.Optic
import qualified Data.Text as T
import qualified Data.Text.Optic as TO


tests :: IO Bool
tests = checkParallel $$(discover)

---------------------------------------------------------------------
-- ByteString splitting
---------------------------------------------------------------------

-- P1: lined round-trip
prop_P1_bs_lined :: Property
prop_P1_bs_lined = property $ do
    -- Note: lines/intercalate round-trip is not exact for trailing newlines
    -- so test with content that doesn't end in newline
    parts <- forAll $ Gen.list (Range.linear 1 5) (Gen.utf8 (Range.linear 1 10) Gen.alpha)
    let bs = B8.intercalate "\n" parts
    review BO.lined (view BO.lined bs) === bs

-- P2: worded round-trip
prop_P2_bs_worded :: Property
prop_P2_bs_worded = property $ do
    parts <- forAll $ Gen.list (Range.linear 1 5) (Gen.utf8 (Range.linear 1 10) Gen.alpha)
    let bs = B8.intercalate " " parts
    review BO.worded (view BO.worded bs) === bs

-- P3: splitOn round-trip
prop_P3_bs_splitOn :: Property
prop_P3_bs_splitOn = property $ do
    parts <- forAll $ Gen.list (Range.linear 1 5) (Gen.utf8 (Range.linear 1 10) Gen.alpha)
    let bs = B8.intercalate "," parts
    review (BO.splitOn ",") (view (BO.splitOn ",") bs) === bs

-- P4: bytes agrees with BS.map
prop_P4_bs_bytes :: Property
prop_P4_bs_bytes = property $ do
    bs <- forAll $ Gen.utf8 (Range.linear 0 50) Gen.alpha
    over BO.bytes (+ 1) bs === B8.map (toEnum . (+ 1) . fromEnum) bs

---------------------------------------------------------------------
-- Text splitting
---------------------------------------------------------------------

-- P5: lined round-trip
prop_P5_text_lined :: Property
prop_P5_text_lined = property $ do
    parts <- forAll $ Gen.list (Range.linear 1 5) (Gen.text (Range.linear 1 10) Gen.alpha)
    let t = T.intercalate "\n" parts
    review TO.lined (view TO.lined t) === t

-- P6: worded round-trip
prop_P6_text_worded :: Property
prop_P6_text_worded = property $ do
    parts <- forAll $ Gen.list (Range.linear 1 5) (Gen.text (Range.linear 1 10) Gen.alpha)
    let t = T.intercalate " " parts
    review TO.worded (view TO.worded t) === t

-- P7: splitOn round-trip
prop_P7_text_splitOn :: Property
prop_P7_text_splitOn = property $ do
    parts <- forAll $ Gen.list (Range.linear 1 5) (Gen.text (Range.linear 1 10) Gen.alpha)
    let t = T.intercalate "," parts
    review (TO.splitOn ",") (view (TO.splitOn ",") t) === t

-- P8: chars agrees with T.map
prop_P8_text_chars :: Property
prop_P8_text_chars = property $ do
    t <- forAll $ Gen.text (Range.linear 0 50) Gen.alpha
    over TO.chars succ t === T.map succ t

---------------------------------------------------------------------
-- Splitting semantics
---------------------------------------------------------------------

-- P9: lined splits on '\n'
prop_P9_lined_splits :: Property
prop_P9_lined_splits = property $ do
    view BO.lined ("hello\nworld" :: B8.ByteString) === ["hello", "world"]
    view TO.lined ("hello\nworld" :: T.Text) === ["hello", "world"]

-- P10: worded splits on ' '
prop_P10_worded_splits :: Property
prop_P10_worded_splits = property $ do
    view BO.worded ("hello world" :: B8.ByteString) === ["hello", "world"]
    view TO.worded ("hello world" :: T.Text) === ["hello", "world"]

-- P11: bytes traverses each byte
prop_P11_bytes_count :: Property
prop_P11_bytes_count = property $ do
    bs <- forAll $ Gen.utf8 (Range.linear 0 50) Gen.alpha
    lists BO.bytes bs === BS.unpack bs

-- P12: chars traverses each char
prop_P12_chars_count :: Property
prop_P12_chars_count = property $ do
    t <- forAll $ Gen.text (Range.linear 0 50) Gen.alpha
    lists TO.chars t === T.unpack t

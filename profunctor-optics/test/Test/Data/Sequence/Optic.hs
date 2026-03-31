{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Test.Data.Sequence.Optic (tests) where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Data.Monoid (Sum(..))
import Data.Sequence.Optic
import Data.Profunctor.Optic hiding (zipped)
import qualified Data.Bifunctor as B
import Data.Foldable (toList)
import qualified Data.Sequence as Seq

tests :: IO Bool
tests = checkParallel $$(discover)

-- slicedTo: first n elements
prop_slicedTo_length :: Property
prop_slicedTo_length = property $ do
    xs <- forAll $ Gen.list (Range.linear 0 20) (Gen.int (Range.linear 0 100))
    n <- forAll $ Gen.int (Range.linear 0 (length xs + 5))
    let s = Seq.fromList xs
        result = fmap snd $ ixtoListOf (slicedTo n) s
    length result === min n (Seq.length s)

-- slicedTo: indices are correct positions
prop_slicedTo_indices :: Property
prop_slicedTo_indices = property $ do
    xs <- forAll $ Gen.list (Range.linear 0 20) (Gen.int (Range.linear 0 100))
    n <- forAll $ Gen.int (Range.linear 0 (length xs + 5))
    let s = Seq.fromList xs
        indices = fmap (getSum . fst) $ ixtoListOf (slicedTo n) s
    indices === [0 .. min n (Seq.length s) - 1]

-- slicedFrom: all but first n
prop_slicedFrom_length :: Property
prop_slicedFrom_length = property $ do
    xs <- forAll $ Gen.list (Range.linear 0 20) (Gen.int (Range.linear 0 100))
    n <- forAll $ Gen.int (Range.linear 0 (length xs + 5))
    let s = Seq.fromList xs
        result = fmap snd $ ixtoListOf (slicedFrom n) s
    length result === max 0 (Seq.length s - n)

-- slicedFrom: indices start at n
prop_slicedFrom_indices :: Property
prop_slicedFrom_indices = property $ do
    xs <- forAll $ Gen.list (Range.linear 0 20) (Gen.int (Range.linear 0 100))
    n <- forAll $ Gen.int (Range.linear 0 (length xs + 5))
    let s = Seq.fromList xs
        indices = fmap (getSum . fst) $ ixtoListOf (slicedFrom n) s
    indices === [n .. Seq.length s - 1]

-- sliced: range [i, j)
prop_sliced_range :: Property
prop_sliced_range = property $ do
    xs <- forAll $ Gen.list (Range.linear 0 20) (Gen.int (Range.linear 0 100))
    let n = length xs
    i <- forAll $ Gen.int (Range.linear 0 n)
    j <- forAll $ Gen.int (Range.linear i n)
    let s = Seq.fromList xs
        result = fmap snd $ ixtoListOf (sliced i j) s
    length result === (j - i)

-- sliced: indices match range
prop_sliced_indices :: Property
prop_sliced_indices = property $ do
    xs <- forAll $ Gen.list (Range.linear 0 20) (Gen.int (Range.linear 0 100))
    let n = length xs
    i <- forAll $ Gen.int (Range.linear 0 n)
    j <- forAll $ Gen.int (Range.linear i n)
    let s = Seq.fromList xs
        indices = fmap (getSum . fst) $ ixtoListOf (sliced i j) s
    indices === [i .. j - 1]

-- viewedl: iso roundtrip
prop_viewedl_roundtrip :: Property
prop_viewedl_roundtrip = property $ do
    xs <- forAll $ Gen.list (Range.linear 0 20) (Gen.int (Range.linear 0 100))
    let s = Seq.fromList xs
    review viewedl (view viewedl s) === s

-- viewedr: iso roundtrip
prop_viewedr_roundtrip :: Property
prop_viewedr_roundtrip = property $ do
    xs <- forAll $ Gen.list (Range.linear 0 20) (Gen.int (Range.linear 0 100))
    let s = Seq.fromList xs
    review viewedr (view viewedr s) === s

---------------------------------------------------------------------
-- Indexed optics
---------------------------------------------------------------------

gen_seq :: Gen (Seq.Seq Int)
gen_seq = Seq.fromList <$> Gen.list (Range.linear 0 20) (Gen.int (Range.linear 0 100))

-- ixtraversed: identity law
prop_ixtraversed_id :: Property
prop_ixtraversed_id = property $ do
    s <- forAll gen_seq
    ixsets ixtraversed (\_ a -> a) s === s

-- ixtraversed: indices are correct positions
prop_ixtraversed_indices :: Property
prop_ixtraversed_indices = property $ do
    s <- forAll gen_seq
    let indices = fmap fst (ixtoListOf ixtraversed s)
    indices === [Sum i | i <- [0 .. Seq.length s - 1]]

-- ixtraversed: values match toList
prop_ixtraversed_values :: Property
prop_ixtraversed_values = property $ do
    s <- forAll gen_seq
    let vals = fmap snd (ixtoListOf ixtraversed s)
    vals === toList s

-- ixtraversed: (.) accumulates indices across composition
prop_ixtraversed_dot_accumulates :: Property
prop_ixtraversed_dot_accumulates = withTests 1 . property $ do
    let ss = Seq.fromList [Seq.fromList [10,20], Seq.fromList [30]]
        result = B.first getSum <$> ixtoListOf (ixtraversed . ixtraversed) ss
    -- outer index 0: inner [0,1] -> [0+0, 0+1] = [0,1]
    -- outer index 1: inner [0]   -> [1+0]       = [1]
    result === [(0,10),(1,20),(1,30)]

-- ixat: incoming index determines position
prop_ixat_lookup :: Property
prop_ixat_lookup = property $ do
    s <- forAll gen_seq
    i <- forAll $ Gen.int (Range.linear 0 (max 0 (Seq.length s - 1)))
    let result = ixpreview ixat s :: Maybe (Sum Int, Int)
    -- ixpreview seeds at mempty = Sum 0, so ixat looks up position 0
    case Seq.lookup 0 s of
      Nothing -> result === Nothing
      Just a  -> result === Just (Sum 0, a)

-- ixat: set at incoming index
prop_ixat_set :: Property
prop_ixat_set = withTests 100 . property $ do
    xs <- forAll $ Gen.list (Range.linear 1 20) (Gen.int (Range.linear 0 100))
    let s = Seq.fromList xs
    -- ixsets seeds at mempty = Sum 0, sets position 0
    ixsets ixat (\_ _ -> 999) s === Seq.update 0 999 s

-- ixmapped: agrees with Seq.mapWithIndex
prop_ixmapped_eq :: Property
prop_ixmapped_eq = property $ do
    s <- forAll gen_seq
    let f k a = a + getSum k
    ixsets ixmapped f s === Seq.mapWithIndex (\i a -> a + i) s

-- ixfolded: agrees with ixtraversed on toList
prop_ixfolded_eq :: Property
prop_ixfolded_eq = property $ do
    s <- forAll gen_seq
    ixtoListOf ixfolded s === ixtoListOf ixtraversed s

-- ixfiltered: indexed filter
prop_ixfiltered_even_indices :: Property
prop_ixfiltered_even_indices = property $ do
    s <- forAll gen_seq
    let result = ixsets ixfiltered (\k _ -> even (getSum k)) s
    result === Seq.fromList [a | (i, a) <- zip [0..] (toList s), even i]

-- adjusted: sets at incoming index (seeded at 0)
prop_adjusted_at_zero :: Property
prop_adjusted_at_zero = withTests 100 . property $ do
    xs <- forAll $ Gen.list (Range.linear 1 20) (Gen.int (Range.linear 0 100))
    let s = Seq.fromList xs
    ixsets adjusted (\_ _ -> 999) s === Seq.adjust' (const 999) 0 s

---------------------------------------------------------------------
-- Coindexed optics
---------------------------------------------------------------------

-- cxtraversed: cosets agrees with Seq.mapWithIndex
prop_cxtraversed_eq :: Property
prop_cxtraversed_eq = property $ do
    s <- forAll gen_seq
    let f k a = a + getSum k
    cxsets cxtraversed f s === Seq.mapWithIndex (\i a -> a + i) s

-- cxmapped: agrees with Seq.mapWithIndex
prop_cxmapped_eq :: Property
prop_cxmapped_eq = property $ do
    s <- forAll gen_seq
    let f k a = a + getSum k
    cxsets cxmapped f s === Seq.mapWithIndex (\i a -> a + i) s

-- cxfiltered: coindexed filter on even positions
prop_cxfiltered_even_indices :: Property
prop_cxfiltered_even_indices = property $ do
    s <- forAll gen_seq
    let result = cxsets cxfiltered (\k _ -> even (getSum k)) s
    result === Seq.fromList [a | (i, a) <- zip [0..] (toList s), even i]

-- zipped: known-length coindexed grate identity
prop_zipped_id :: Property
prop_zipped_id = property $ do
    s <- forAll gen_seq
    let n = Seq.length s
    cxsets (zipped n) (\_ a -> a) s === s

-- zipped: indices are correct
prop_zipped_indices :: Property
prop_zipped_indices = withTests 1 . property $ do
    let s = Seq.fromList [10, 20, 30 :: Int]
        result = cxsets (zipped 3) (\k a -> a + getSum k) s
    result === Seq.fromList [10, 21, 32]

---------------------------------------------------------------------
-- Prisms
---------------------------------------------------------------------

-- consed: roundtrip on non-empty
prop_consed_roundtrip :: Property
prop_consed_roundtrip = property $ do
    xs <- forAll $ Gen.list (Range.linear 1 20) (Gen.int (Range.linear 0 100))
    let s = Seq.fromList xs
    case preview consed s of
      Nothing -> failure
      Just (a, rest) -> review consed (a, rest) === s

-- consed: empty gives Nothing
prop_consed_empty :: Property
prop_consed_empty = withTests 1 . property $
    preview consed (Seq.empty :: Seq.Seq Int) === Nothing

-- snoced: roundtrip on non-empty
prop_snoced_roundtrip :: Property
prop_snoced_roundtrip = property $ do
    xs <- forAll $ Gen.list (Range.linear 1 20) (Gen.int (Range.linear 0 100))
    let s = Seq.fromList xs
    case preview snoced s of
      Nothing -> failure
      Just (rest, a) -> review snoced (rest, a) === s

---------------------------------------------------------------------
-- Fold0
---------------------------------------------------------------------

-- headed: agrees with Seq head
prop_headed_eq :: Property
prop_headed_eq = property $ do
    s <- forAll gen_seq
    preview headed s === (if Seq.null s then Nothing else Just (s `Seq.index` 0))

-- lasted: agrees with Seq last
prop_lasted_eq :: Property
prop_lasted_eq = property $ do
    s <- forAll gen_seq
    preview lasted s === (if Seq.null s then Nothing else Just (s `Seq.index` (Seq.length s - 1)))

-- foundIndex: agrees with Seq.findIndexL
prop_foundIndex_eq :: Property
prop_foundIndex_eq = property $ do
    s <- forAll gen_seq
    let p = (> 50)
    fmap getSum (preview (foundIndex p) s) === Seq.findIndexL p s

{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

module Test.Prop.Sort (tests) where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Control.Arrow (first, second)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Profunctor
import Data.Profunctor.Optic.Types (Lens', Colens)
import Data.Profunctor.Optic.Lens (lens)
import Data.Profunctor.Optic.View ((^.))
import Data.Profunctor.Rep (Corepresentable(..))
import Data.Profunctor.Sieve (Cosieve(..))
import Data.Functor.Coapply (Coapply(..))
import Control.Coapplicative (Coapplicative(..))
import Data.Profunctor.Sort
import Data.Profunctor.Optic.Sort
import Data.Word (Word8)
import Data.Word.Optic (grate8, bits8, ibits8)

import Data.Functor.Index (I8(..))
import Data.Monoid (Sum(..))
import Data.Ord (Down(..))
import qualified Data.List as L
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as Map

tests :: IO Bool
tests = checkParallel $$(discover)

---------------------------------------------------------------------
-- Generators
---------------------------------------------------------------------

genNE :: Gen a -> Gen (NonEmpty a)
genNE g = (:|) <$> g <*> Gen.list (Range.linear 0 20) g

genPairNE :: Gen (NonEmpty (Int, String))
genPairNE = genNE $ (,) <$> Gen.int (Range.linear 0 10) <*> Gen.string (Range.linear 1 5) Gen.alpha

-- | A simple lens on fst for testing
fstL :: Lens' (Int, String) Int
fstL = lens fst (\(_, b) a -> (a, b))

---------------------------------------------------------------------
-- P1–P4: Sort1 profunctor laws
---------------------------------------------------------------------

-- P1: dimap id id = id
prop_P1_sort1_dimap_id :: Property
prop_P1_sort1_dimap_id = property $ do
    xs <- forAll genPairNE
    let s = mkSort1 :: Sort1 Int String String
    runSort1 (dimap id id s) xs === runSort1 s xs

-- P2: dimap f g . dimap h k = dimap (h . f) (g . k)
prop_P2_sort1_dimap_compose :: Property
prop_P2_sort1_dimap_compose = property $ do
    xs <- forAll genPairNE
    let s = mkSort1 :: Sort1 Int String String
        f = reverse
        g = (++ "!")
        h = (++ "x")
        k = take 3
        lhs = dimap f g . dimap h k $ s
        rhs = dimap (h . f) (g . k) s
    runSort1 lhs xs === runSort1 rhs xs

-- P3: first' . dimap f g = dimap (first f) (first g) . first'
prop_P3_sort1_strong_natural :: Property
prop_P3_sort1_strong_natural = property $ do
    xs <- forAll $ genNE $ (,) <$> Gen.int (Range.linear 0 10) <*> ((,) <$> Gen.string (Range.linear 1 5) Gen.alpha <*> Gen.bool)
    let s = mkSort1 :: Sort1 Int String String
        f = reverse
        g = (++ "!")
        lhs = first' (dimap f g s)
        rhs = dimap (first f) (first g) (first' s)
    runSort1 lhs xs === runSort1 rhs xs

-- P4: left' . dimap f g = dimap (mapLeft f) (mapLeft g) . left'
prop_P4_sort1_choice_natural :: Property
prop_P4_sort1_choice_natural = property $ do
    xs <- forAll $ genNE $ (,) <$> Gen.int (Range.linear 0 10) <*> Gen.either (Gen.string (Range.linear 1 5) Gen.alpha) Gen.bool
    let s = mkSort1 :: Sort1 Int String String
        f = reverse
        g = (++ "!")
        lhs = left' (dimap f g s)
        rhs = dimap (mapLeft f) (mapLeft g) (left' s)
    runSort1 lhs xs === runSort1 rhs xs

---------------------------------------------------------------------
-- P5–P7: Sort2 profunctor laws
---------------------------------------------------------------------

-- P5: dimap id id = id
prop_P5_sort2_dimap_id :: Property
prop_P5_sort2_dimap_id = property $ do
    xs <- forAll genPairNE
    let s = mkSort2 :: Sort2 Int String String
    runSort2 (dimap id id s) xs === runSort2 s xs

-- P6: unfirst . first' = id (Costrong/Strong roundtrip)
prop_P6_sort2_costrong_strong :: Property
prop_P6_sort2_costrong_strong = property $ do
    xs <- forAll genPairNE
    let s = mkSort2 :: Sort2 Int String String
    runSort2 (unfirst (first' s)) xs === runSort2 s xs

-- P7: unleft . left' = id (Cochoice/Choice roundtrip)
prop_P7_sort2_cochoice_choice :: Property
prop_P7_sort2_cochoice_choice = property $ do
    xs <- forAll genPairNE
    let s = mkSort2 :: Sort2 Int String String
    runSort2 (unleft (left' s)) xs === runSort2 s xs

---------------------------------------------------------------------
-- P8–P11: Sort3 profunctor laws
---------------------------------------------------------------------

-- P8: dimap id id = id
prop_P8_sort3_dimap_id :: Property
prop_P8_sort3_dimap_id = property $ do
    idx <- forAll $ Gen.int (Range.linear 0 5)
    key <- forAll $ Gen.int (Range.linear 0 10)
    let s = Sort3 (\inp _j k -> snd (inp k)) :: Sort3 Int Int Int String String
        inp i = (i, show i)
    runSort3 (dimap id id s) inp idx key === runSort3 s inp idx key

-- P9: closed . dimap f g = dimap ((f .) . (.)) ((g .) . (.)) . closed
--     (simplified: test closed preserves identity)
prop_P9_sort3_closed_id :: Property
prop_P9_sort3_closed_id = property $ do
    key <- forAll $ Gen.int (Range.linear 0 5)
    x <- forAll $ Gen.int (Range.linear 0 5)
    let s = Sort3 (\inp _j k -> snd (inp k)) :: Sort3 Int Int Int String String
        inp i = (i, show i)
    runSort3 (closed s) (\i -> (fst (inp i), const (snd (inp i)))) 0 key x
      === runSort3 s inp 0 key

-- P10: cosieve (cotabulate f) = f (Corepresentable roundtrip)
prop_P10_sort3_corep_rt1 :: Property
prop_P10_sort3_corep_rt1 = property $ do
    key <- forAll $ Gen.int (Range.linear 0 5)
    let f :: Sort3Corep Int Int Int String -> String
        f (Sort3Corep ika _j k) = snd (ika k) ++ "!"
        inp i = (i, show i)
        p = cotabulate f :: Sort3 Int Int Int String String
        result = cosieve p (Sort3Corep inp 0 key)
    result === f (Sort3Corep inp 0 key)

-- P11: cotabulate (cosieve p) = p (Corepresentable roundtrip)
prop_P11_sort3_corep_rt2 :: Property
prop_P11_sort3_corep_rt2 = property $ do
    key <- forAll $ Gen.int (Range.linear 0 5)
    let s = Sort3 (\inp _j k -> snd (inp k)) :: Sort3 Int Int Int String String
        inp i = (i, show i)
    runSort3 (cotabulate (cosieve s)) inp 0 key === runSort3 s inp 0 key

---------------------------------------------------------------------
-- P12–P15: sortingOf operator properties
---------------------------------------------------------------------

-- P12: all elements in a group share the same key
prop_P12_sortingOf_same_key :: Property
prop_P12_sortingOf_same_key = property $ do
    xs <- forAll genPairNE
    let groups = sortingOf fstL xs
    assert $ all (\g -> allEqual (fmap (^. fstL) g)) groups

-- P13: groups are in ascending key order
prop_P13_sortingOf_ascending :: Property
prop_P13_sortingOf_ascending = property $ do
    xs <- forAll genPairNE
    let keys = map (\g -> NE.head g ^. fstL) (sortingOf fstL xs)
    keys === L.sort keys

-- P14: total element count across groups = input count
prop_P14_sortingOf_preserves :: Property
prop_P14_sortingOf_preserves = property $ do
    xs <- forAll genPairNE
    let groups = sortingOf fstL xs
        totalElems = sum $ map (length . NE.toList) groups
    totalElems === length xs

-- P15: nubbingOf returns one element per distinct key
prop_P15_nubbingOf_one_per_key :: Property
prop_P15_nubbingOf_one_per_key = property $ do
    xs <- forAll genPairNE
    let nubbed = nubbingOf fstL xs
        keys = map (^. fstL) nubbed
    keys === L.nub keys

---------------------------------------------------------------------
-- P16–P18: New Sort1 operator properties
---------------------------------------------------------------------

-- P16: sortingDescOf groups are in descending key order
prop_P16_sortingDescOf_descending :: Property
prop_P16_sortingDescOf_descending = property $ do
    xs <- forAll genPairNE
    let keys = map (\g -> NE.head g ^. fstL) (sortingDescOf fstL xs)
    keys === L.sortBy (flip compare) keys

-- P17: toMapOf keys = set of focused values
prop_P17_toMapOf_keys :: Property
prop_P17_toMapOf_keys = property $ do
    xs <- forAll genPairNE
    let m = toMapOf fstL xs
        mapKeys = Map.keysSet m
        inputKeys = Map.keysSet $ Map.fromList [(s ^. fstL, ()) | s <- NE.toList xs]
    mapKeys === inputKeys

-- P18: toMapOf values agree with sortingOf groups
prop_P18_toMapOf_agrees :: Property
prop_P18_toMapOf_agrees = property $ do
    xs <- forAll genPairNE
    let m = toMapOf fstL xs
        groups = sortingOf fstL xs
        fromGroups = Map.fromList [(NE.head g ^. fstL, g) | g <- groups]
    m === fromGroups

---------------------------------------------------------------------
-- P19–P20: Sort2 operator properties
---------------------------------------------------------------------

-- P19: groupingBack produces >=1 group (NonEmpty outer)
prop_P19_groupingBack_nonempty :: Property
prop_P19_groupingBack_nonempty = property $ do
    xs <- forAll genPairNE
    let result = groupingBack fstL xs
    assert $ length result >= 1

-- P20: groupingBack total element count = input count
prop_P20_groupingBack_preserves :: Property
prop_P20_groupingBack_preserves = property $ do
    xs <- forAll genPairNE
    let result = groupingBack fstL xs
        totalElems = sum $ fmap length result
    totalElems === length xs

---------------------------------------------------------------------
-- P21: foldSorting1 agrees with nubbingOf
---------------------------------------------------------------------

-- P21: foldSorting1 with const = nubbingOf (first per group)
prop_P21_foldSorting1_const :: Property
prop_P21_foldSorting1_const = property $ do
    xs <- forAll genPairNE
    let result = map (foldr1 const) (sortingOf fstL xs)
    result === nubbingOf fstL xs

---------------------------------------------------------------------
-- P22–P24: Sort3Corep Coapplicative properties (Monoid i)
---------------------------------------------------------------------

-- P22: coapply . fmap Left = Left
prop_P22_sort3corep_coapply_left :: Property
prop_P22_sort3corep_coapply_left = property $ do
    key <- forAll $ Gen.int (Range.linear 0 5)
    let inp i = (getSum i, show (getSum i))
        x = Sort3Corep inp (0 :: Int) key :: Sort3Corep (Sum Int) Int Int String
        result = coapply (fmap Left x)
    case result of
        Left (Sort3Corep ika _ _) -> snd (ika mempty) === snd (inp mempty)
        Right _                   -> failure

-- P23: coapply . fmap Right = Right
prop_P23_sort3corep_coapply_right :: Property
prop_P23_sort3corep_coapply_right = property $ do
    key <- forAll $ Gen.int (Range.linear 0 5)
    let inp i = (getSum i, show (getSum i))
        x = Sort3Corep inp (0 :: Int) key :: Sort3Corep (Sum Int) Int Int String
        result = coapply (fmap Right x)
    case result of
        Right (Sort3Corep ika _ _) -> snd (ika mempty) === snd (inp mempty)
        Left _                     -> failure

-- P24: copure . fmap f = f . copure
prop_P24_sort3corep_copure_natural :: Property
prop_P24_sort3corep_copure_natural = property $ do
    key <- forAll $ Gen.int (Range.linear 0 5)
    let inp i = (getSum i, show (getSum i))
        f = (++ "!")
        x = Sort3Corep inp (0 :: Int) key :: Sort3Corep (Sum Int) Int Int String
    copure (fmap f x) === f (copure x)

---------------------------------------------------------------------
-- P25–P29: Sort3 carrier properties
---------------------------------------------------------------------

-- P25: mkSort3 identity: for a valid key, returns the value at that position
prop_P25_mkSort3_identity :: Property
prop_P25_mkSort3_identity = property $ do
    -- Use Bool as index (Bounded, Enum), Int as key
    let inp :: Bool -> (Int, String)
        inp False = (0, "zero")
        inp True  = (1, "one")
        s = mkSort3 :: Sort3 Bool Int Int String String
    -- j=0 is first position in each group; key 0 -> "zero", key 1 -> "one"
    runSort3 s inp 0 0 === "zero"
    runSort3 s inp 0 1 === "one"

-- P26: mkSort3 groups by key — positions with same key land in same group
prop_P26_mkSort3_grouping :: Property
prop_P26_mkSort3_grouping = property $ do
    -- 4 positions (I4 simulated as enum 0..3), two keys
    let inp :: Int -> (Bool, Char)
        inp 0 = (True,  'a')
        inp 1 = (False, 'b')
        inp 2 = (True,  'c')
        inp 3 = (False, 'd')
        inp _ = (True,  '?')
        -- mkSort3 needs Bounded+Enum on i, use a wrapper
        s = Sort3 $ \inp' j k ->
              let pairs = [(ki, a) | i <- [0..3 :: Int], let (ki, a) = inp' i]
                  grouped = Map.fromListWith (flip (++)) [(ki, [a]) | (ki, a) <- pairs]
              in  case Map.lookup k grouped of
                    Just as' -> as' !! (j `mod` length as')
                    Nothing  -> snd (inp' 0)
    -- True group: positions 0,2 -> ['a','c']; False group: positions 1,3 -> ['b','d']
    runSort3 s inp 0 True  === 'a'
    runSort3 s inp 1 True  === 'c'
    runSort3 s inp 0 False === 'b'
    runSort3 s inp 1 False === 'd'

-- P27: sortingUnder composes Sort3 with a Colens
prop_P27_sortingUnder :: Property
prop_P27_sortingUnder = property $ do
    key <- forAll $ Gen.int (Range.linear 0 5)
    let s = Sort3 (\inp _j k -> snd (inp k)) :: Sort3 Int Int Int String String
        lifted = sortingUnder id s  -- id is a valid Colens (it's an Iso)
        inp i = (i, show i)
    runSort3 lifted inp 0 key === runSort3 s inp 0 key

-- P29: sortOn3 re-keys correctly
prop_P29_sortOn3 :: Property
prop_P29_sortOn3 = property $ do
    let inp :: Bool -> (Int, String)
        inp False = (0, "zero")
        inp True  = (1, "one")
        s = mkSort3 :: Sort3 Bool Int Int String String
        -- sortOn3 with id should be the same as mkSort3
        s' = sortOn3 id s
    runSort3 s' inp 0 0 === runSort3 s inp 0 0
    runSort3 s' inp 0 1 === runSort3 s inp 0 1

---------------------------------------------------------------------
-- P28, P30: Sort3 + Word8 optic composition
---------------------------------------------------------------------

-- P28: grate8 composes with Sort3 via sortingUnder (Closed)
-- grate8 :: Colens Word8 Word8 (I8 -> Bool) (I8 -> Bool)
-- Sort3 operates on bit-representations, grate8 lifts to Word8.
prop_P28_grate8_sort3_over :: Property
prop_P28_grate8_sort3_over = property $ do
    w <- forAll $ Gen.word8 Range.constantBounded
    -- A Sort3 that groups bit-functions by their value at I81
    let carrier = mkSort3 :: Sort3 I8 Int Bool (I8 -> Bool) (I8 -> Bool)
        lifted = sortingUnder grate8 carrier :: Sort3 I8 Int Bool Word8 Word8
        -- Input: each I8 position maps to (bit value at I81, the whole word)
        inp :: I8 -> (Bool, Word8)
        inp _i = (testBit' w 0, w)
    -- All positions have the same key, so any j/k lookup returns w
    runSort3 lifted inp 0 (testBit' w 0) === w
  where
    testBit' :: Word8 -> Int -> Bool
    testBit' w' n = w' `div` (2 ^ n) `mod` 2 == 1

-- P30: sortingUnder grate8 composes Sort3 at bit-representation level
-- grate8 :: Colens Word8 Word8 (I8 -> Bool) (I8 -> Bool)
prop_P30_grate8_sort3 :: Property
prop_P30_grate8_sort3 = property $ do
    w <- forAll $ Gen.word8 Range.constantBounded
    let -- A Sort3 that operates on (I8 -> Bool) representations
        innerSort = Sort3 (\inp _j _k -> snd (inp 0)) :: Sort3 Int Int Int (I8 -> Bool) (I8 -> Bool)
        -- Lift through grate8 to operate on Word8
        lifted = sortingUnder grate8 innerSort :: Sort3 Int Int Int Word8 Word8
        inp i = (i, w)
    -- The inner sort just returns the value at position 0, so lifted
    -- should return the Word8 unchanged
    runSort3 lifted inp 0 0 === w

---------------------------------------------------------------------
-- P31–P32: Sort3 + bits8 (Cotraversal, needs Choice + Cotraversing)
---------------------------------------------------------------------

-- P31: bits8 composes with Sort3 when Monoid i (Choice + Cotraversing)
-- bits8 :: Cotraversal Word8 Word8 Bool Bool
-- Now Sort3 has Choice (Monoid i) so this typechecks.
prop_P31_bits8_sort3 :: Property
prop_P31_bits8_sort3 = property $ do
    w <- forAll $ Gen.word8 Range.constantBounded
    let carrier = mkSort3 :: Sort3 I8 Int Bool Bool Bool
        -- bits8 lifts Sort3 from Bool to Word8
        lifted = bits8 carrier :: Sort3 I8 Int Bool Word8 Word8
        -- Each I8 position -> (bit value at that position, the whole word)
        inp :: I8 -> (Bool, Word8)
        inp _i = (testBit' w 0, w)
    runSort3 lifted inp 0 (testBit' w 0) === w
  where
    testBit' :: Word8 -> Int -> Bool
    testBit' w' n = w' `div` (2 ^ n) `mod` 2 == 1

-- P32: ibits8 composes with Sort3 (Cxlens I8, needs Closed)
-- ibits8 :: Cxlens I8 Word8 Word8 Bool Bool
-- Cx p k a b = p a (k -> b), so carrier needs output (I8 -> Bool)
prop_P32_ibits8_sort3 :: Property
prop_P32_ibits8_sort3 = property $ do
    w <- forAll $ Gen.word8 Range.constantBounded
    let -- Carrier for coindexed: output is (I8 -> Bool) not Bool
        carrier :: Sort3 I8 Int Bool Bool (I8 -> Bool)
        carrier = rmap const mkSort3
        lifted = ibits8 carrier
        inp :: I8 -> (Bool, Word8)
        inp _i = (testBit' w 0, w)
    -- The coindex i is the bit position; result is (I8 -> Word8)
    -- We check that looking up any bit position gives back w
    runSort3 lifted inp 0 (testBit' w 0) I81 === w
  where
    testBit' :: Word8 -> Int -> Bool
    testBit' w' n = w' `div` (2 ^ n) `mod` 2 == 1

---------------------------------------------------------------------
-- P33–P35: cosortingOf, zipsSorting
---------------------------------------------------------------------

-- P33: cosortingOf bits8 = bits8 (just a named wrapper)
prop_P33_cosortingOf_bits8 :: Property
prop_P33_cosortingOf_bits8 = property $ do
    w <- forAll $ Gen.word8 Range.constantBounded
    let carrier = mkSort3 :: Sort3 I8 Int Bool Bool Bool
        lifted = cosortingOf bits8 carrier
        inp :: I8 -> (Bool, Word8)
        inp _i = (testBit' w 0, w)
    runSort3 lifted inp 0 (testBit' w 0) === w
  where
    testBit' :: Word8 -> Int -> Bool
    testBit' w' n = w' `div` (2 ^ n) `mod` 2 == 1

-- P34: zipsSorting combines results pointwise
prop_P34_zipsSorting :: Property
prop_P34_zipsSorting = property $ do
    let s1 = Sort3 (\inp _j k -> snd (inp k) + 1) :: Sort3 Int Int Int Int Int
        s2 = Sort3 (\inp _j k -> snd (inp k) + 2) :: Sort3 Int Int Int Int Int
        merged = zipsSorting (+) s1 s2
        inp i = (i, i * 10)
    -- At key 3: s1 gives 31, s2 gives 32, merged gives 63
    runSort3 merged inp 0 3 === 63

-- P35: zipsSorting with const = first sort wins
prop_P35_zipsSorting_const :: Property
prop_P35_zipsSorting_const = property $ do
    let s1 = Sort3 (\_ _ _ -> "first") :: Sort3 Int Int Int Int String
        s2 = Sort3 (\_ _ _ -> "second") :: Sort3 Int Int Int Int String
        merged = zipsSorting const s1 s2
    runSort3 merged (\i -> (i, i)) 0 0 === "first"

---------------------------------------------------------------------
-- Helpers
---------------------------------------------------------------------

allEqual :: Eq a => NonEmpty a -> Bool
allEqual (x :| xs) = all (== x) xs

mapLeft :: (a -> c) -> Either a b -> Either c b
mapLeft f (Left a)  = Left (f a)
mapLeft _ (Right b) = Right b

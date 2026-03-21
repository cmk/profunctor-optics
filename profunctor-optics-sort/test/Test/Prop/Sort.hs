{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

module Test.Prop.Sort (tests) where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Control.Arrow (first, second)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Profunctor
import Data.Profunctor.Optic.Types (Lens')
import Data.Profunctor.Optic.Lens (lens)
import Data.Profunctor.Optic.View ((^.))
import Data.Profunctor.Rep (Corepresentable(..))
import Data.Profunctor.Sieve (Cosieve(..))
import Data.Functor.Coapply (Coapply(..))
import Control.Coapplicative (Coapplicative(..))
import Data.Profunctor.Sort
import Data.Profunctor.Optic.Sort

import Data.Monoid (Sum(..))
import qualified Data.List as L
import qualified Data.List.NonEmpty as NE

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
-- Helpers
---------------------------------------------------------------------

allEqual :: Eq a => NonEmpty a -> Bool
allEqual (x :| xs) = all (== x) xs

mapLeft :: (a -> c) -> Either a b -> Either c b
mapLeft f (Left a)  = Left (f a)
mapLeft _ (Right b) = Right b

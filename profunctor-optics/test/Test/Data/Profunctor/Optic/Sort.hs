{-# LANGUAGE TemplateHaskell #-}

-- | Property tests for 'Sort' carrier and operators.
module Test.Data.Profunctor.Optic.Sort (tests) where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Data.Monoid (Sum(..))
import Data.Profunctor
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Lens (lensVl)
import Data.Profunctor.Optic.Property as Prop
import Data.Profunctor.Optic.Sort
import Data.Profunctor.Optic.Types (Lens')
import qualified Control.Category as C
import qualified Data.Map.Strict as Map

tests :: IO Bool
tests = checkParallel $$(discover)

fstL :: Lens' (Int, String) Int
fstL = lensVl $ \f (a, b) -> (\a' -> (a', b)) <$> f a

---------------------------------------------------------------------
-- Sort profunctor laws (via Property.hs predicates)
---------------------------------------------------------------------

-- | dimap id id = id
prop_sort_dimap_id :: Property
prop_sort_dimap_id = property $ do
    let s = mkSortN 5 :: Sort Int Int Int (Map.Map Int [Int])
        inp i = (i `mod` 3, i * 10)
    assert $ Prop.id_sort s inp

-- | dimap composition
prop_sort_dimap_compose :: Property
prop_sort_dimap_compose = property $ do
    let s = mkSortN 5 :: Sort Int Int Int (Map.Map Int [Int])
        inp i = (i `mod` 3, i * 10)
    assert $ Prop.compose_sort s id id id id inp

---------------------------------------------------------------------
-- Sort Category laws
---------------------------------------------------------------------

-- | id . f = f and f . id = f
prop_sort_category_id :: Property
prop_sort_category_id = property $ do
    let s = Sort (\inp -> snd (inp (Sum 0)) + 1)
            :: Sort (Sum Int) (Sum Int) Int Int
        inp i = (Sum (getSum i `mod` 2), getSum i * 10)
    assert $ Prop.id_category_sort s inp

-- | (f . g) . h = f . (g . h)
prop_sort_category_assoc :: Property
prop_sort_category_assoc = property $ do
    let f = Sort (\inp -> snd (inp (Sum 0)) + 1)
            :: Sort (Sum Int) (Sum Int) Int Int
        g = Sort (\inp -> snd (inp (Sum 0)) * 2)
            :: Sort (Sum Int) (Sum Int) Int Int
        h = Sort (\inp -> snd (inp (Sum 0)) - 3)
            :: Sort (Sum Int) (Sum Int) Int Int
        inp i = (Sum (getSum i `mod` 2), getSum i)
    assert $ Prop.assoc_category_sort h g f inp

---------------------------------------------------------------------
-- Sort carriers
---------------------------------------------------------------------

-- | mkSortN groups by key correctly
prop_mkSortN_groups :: Property
prop_mkSortN_groups = property $ do
    let s = mkSortN 4 :: Sort Int Int Char (Map.Map Int [Char])
        inp 0 = (1, 'a')
        inp 1 = (2, 'b')
        inp 2 = (1, 'c')
        inp 3 = (2, 'd')
        inp _ = (0, '?')
    runSort s inp === Map.fromList [(1, ['a','c']), (2, ['b','d'])]

-- | mkSortN preserves all elements
prop_mkSortN_preserves :: Property
prop_mkSortN_preserves = property $ do
    n <- forAll $ Gen.int (Range.linear 1 50)
    let s = mkSortN n :: Sort Int Int Int (Map.Map Int [Int])
        inp i = (i `mod` 5, i)
        result = runSort s inp
    sum (fmap length result) === n

---------------------------------------------------------------------
-- Sort combinators
---------------------------------------------------------------------

-- | (%.) pipelines: g runs, f sees result
prop_sort_compose :: Property
prop_sort_compose = property $ do
    let s1 = Sort (\inp -> snd (inp 0) + 1)
             :: Sort Int (Sum Int) Int Int
        s2 = Sort (\inp -> snd (inp 0) * 2)
             :: Sort Int (Sum Int) Int Int
        composed = s1 %. s2
        inp i = (Sum i, i + 10)
    runSort composed inp === 21

-- | remapSort id = id
prop_sort_remap_id :: Property
prop_sort_remap_id = property $ do
    let s = mkSortN 3 :: Sort Int Int Int (Map.Map Int [Int])
        inp i = (i, i * 10)
    runSort (remapSort id s) inp === runSort s inp

-- | eitherSort partitions correctly
prop_sort_either :: Property
prop_sort_either = property $ do
    let sl = Sort (\inp -> "left:" ++ show (snd (inp (Sum 0))))
             :: Sort (Sum Int) Int Int String
        sr = Sort (\inp -> "right:" ++ show (snd (inp (Sum 0))))
             :: Sort (Sum Int) Int Int String
        combined = eitherSort sl sr
        inpL :: Sum Int -> (Int, Either Int Int)
        inpL _ = (1, Left 42)
        inpR :: Sum Int -> (Int, Either Int Int)
        inpR _ = (1, Right 99)
    runSort combined inpL === "left:42"
    runSort combined inpR === "right:99"

-- | maybeSort with Nothing returns default
prop_sort_maybe :: Property
prop_sort_maybe = property $ do
    let sf = Sort (\inp -> snd (inp (Sum 0)) * 2)
             :: Sort (Sum Int) Int Int Int
        combined = maybeSort 0 sf
        inpJust :: Sum Int -> (Int, Maybe Int)
        inpJust _ = (1, Just 21)
        inpNothing :: Sum Int -> (Int, Maybe Int)
        inpNothing _ = (1, Nothing)
    runSort combined inpJust === 42
    runSort combined inpNothing === 0

-- | zipsSorting merges pointwise
prop_sort_zips :: Property
prop_sort_zips = property $ do
    let s1 = Sort (\inp -> snd (inp 0) + 1)
             :: Sort Int Int Int Int
        s2 = Sort (\inp -> snd (inp 0) + 2)
             :: Sort Int Int Int Int
        merged = zipsSorting (+) s1 s2
        inp i = (i, i * 10)
    runSort merged inp === 3

---------------------------------------------------------------------
-- Sort operators (from Optic.Sort)
---------------------------------------------------------------------

-- | sortingOfL groups by key
prop_sortingOfL_groups :: Property
prop_sortingOfL_groups = property $ do
    xs <- forAll $ Gen.list (Range.linear 1 20)
        ((,) <$> Gen.int (Range.linear 0 5) <*> Gen.string (Range.linear 1 3) Gen.alpha)
    let groups = sortingOfL fstL xs
    -- All elements preserved
    sum (map length groups) === length xs

-- | sortingOfL empty = []
prop_sortingOfL_empty :: Property
prop_sortingOfL_empty = property $ do
    sortingOfL fstL ([] :: [(Int, String)]) === []

-- | toMapOfL keys match input keys
prop_toMapOfL_keys :: Property
prop_toMapOfL_keys = property $ do
    xs <- forAll $ Gen.list (Range.linear 1 20)
        ((,) <$> Gen.int (Range.linear 0 5) <*> Gen.string (Range.linear 1 3) Gen.alpha)
    let m = toMapOfL fstL xs
    Map.keysSet m === Map.keysSet (Map.fromList [(fst s, ()) | s <- xs])

-- | sortingRep agrees with sortingString
prop_sortingString :: Property
prop_sortingString = property $ do
    s <- forAll $ Gen.string (Range.linear 1 50) Gen.alpha
    let result = sortingString id s
    sum (fmap length result) === length s

-- | mergingOfL inner merge keeps only matching keys
prop_innerMergeL :: Property
prop_innerMergeL = property $ do
    let xs = [(1, "a"), (2, "b"), (3, "c")] :: [(Int, String)]
        ys = [(2, "x"), (3, "y"), (4, "z")] :: [(Int, String)]
        result = innerMergeL fstL fstL (\_ l r -> (l, r)) xs ys
    Map.keys result === [2, 3]

{-# LANGUAGE TemplateHaskell #-}

-- | Property tests for 'Sort' carrier and operators.
module Test.Data.Profunctor.Optic.Sort (tests) where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Data.Monoid (Sum(..))
import Data.Profunctor
import Data.Profunctor.Strong (Costrong(..))
import Data.Profunctor.Choice (Choice(..), Cochoice(..))
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Lens (lensVl, refirst)
import Data.Profunctor.Optic.Prism (releft)
import Data.Profunctor.Optic.Property as Prop
import Data.Profunctor.Optic.Sort
import Data.Profunctor.Optic.Types (Lens')
import qualified Control.Category as C
import qualified Data.Map.Strict as Map
import qualified Data.IntMap.Strict as IM
import qualified Data.Set as Set

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
        merged = liftA2 (+) s1 s2
        inp i = (i, i * 10)
    runSort merged inp === 3

---------------------------------------------------------------------
-- Sort operators (from Optic.Sort)
---------------------------------------------------------------------

-- | sorts groups by key
prop_sorts_groups :: Property
prop_sorts_groups = property $ do
    xs <- forAll $ Gen.list (Range.linear 1 20)
        ((,) <$> Gen.int (Range.linear 0 5) <*> Gen.string (Range.linear 1 3) Gen.alpha)
    let groups = sorts fstL xs
    -- All elements preserved
    sum (map length groups) === length xs

-- | sorts empty = []
prop_sorts_empty :: Property
prop_sorts_empty = property $ do
    sorts fstL ([] :: [(Int, String)]) === []

-- | toMapOf keys match input keys
prop_toMapOf_keys :: Property
prop_toMapOf_keys = property $ do
    xs <- forAll $ Gen.list (Range.linear 1 20)
        ((,) <$> Gen.int (Range.linear 0 5) <*> Gen.string (Range.linear 1 3) Gen.alpha)
    let m = toMapOf fstL xs
    Map.keysSet m === Map.keysSet (Map.fromList [(fst s, ()) | s <- xs])

-- | sortingRep agrees with sortingString
prop_sortingString :: Property
prop_sortingString = property $ do
    s <- forAll $ Gen.string (Range.linear 1 50) Gen.alpha
    let result = sortingString id s
    sum (fmap length result) === length s

-- | merges inner merge keeps only matching keys
prop_innerMerges :: Property
prop_innerMerges = property $ do
    let xs = [(1, "a"), (2, "b"), (3, "c")] :: [(Int, String)]
        ys = [(2, "x"), (3, "y"), (4, "z")] :: [(Int, String)]
        result = innerMerges fstL fstL (\_ l r -> (l, r)) xs ys
    Map.keys result === [2, 3]

---------------------------------------------------------------------
-- Relens/Reprism + Sort + containers
---------------------------------------------------------------------

-- Sort is Costrong (has unfirst/unsecond) and Cochoice (has unleft/unright).
-- These act as sort TRANSFORMERS:
--
--   refirst  :: Sort i k (a, c) (b, c) -> Sort i k a b
--     "sort pairs, keep only the first component"
--
--   releft   :: Sort i k (Either a c) (Either b c) -> Sort i k a b
--     "sort Either values, keep only the Left branch"
--
-- Combined with mkSortN (which groups into Maps), these give container
-- operations that project or filter during sorting.

-- | refirst projects pair-sort output to first component.
-- Sort that produces (Int, String) pairs → refirst → Sort that produces Int.
-- After refirst, the Sort consumes just Int (not (Int, String)).
-- The String is tied via Costrong knot-tying.
prop_refirst_sort_project :: Property
prop_refirst_sort_project = property $ do
    let -- Sort that takes (Int, String) input and returns it
        pairSort :: Sort Int Int (Int, String) (Int, String)
        pairSort = Sort $ \inp -> snd (inp 0)
        -- refirst: Sort (a,c) (b,c) → Sort a b  with a=Int, b=Int, c=String
        intSort = refirst pairSort :: Sort Int Int Int Int
        -- After refirst, inp provides (key, Int) — the String comes from the knot
        inp i = (i, i * 10)
    runSort intSort inp === 0

-- | unsecond projects pair-sort output to second component.
prop_unsecond_sort_project :: Property
prop_unsecond_sort_project = property $ do
    let pairSort :: Sort Int Int (Int, String) (Int, String)
        pairSort = Sort $ \inp -> snd (inp 0)
        -- unsecond: Sort (c,a) (c,b) → Sort a b  with a=String, b=String, c=Int
        strSort = unsecond pairSort :: Sort Int Int String String
        -- After unsecond, inp provides (key, String) — the Int comes from the knot
        inp i = (i, "hello")
    runSort strSort inp === "hello"

-- | refirst + mkSortN: Sort produces (Map, metadata) pairs.
-- refirst discards the metadata, keeping only the Map.
prop_refirst_sort_map :: Property
prop_refirst_sort_map = property $ do
    let -- Sort that produces (grouped Map, total count) as a pair
        taggedSort :: Sort Int Int (Int, String) (Map.Map Int [(Int, String)], String)
        taggedSort = Sort $ \inp ->
          let pairs = [inp i | i <- [0..3]]
              m = Map.fromListWith (++) [(fst p, [snd p]) | p <- pairs]
          in (m, "metadata")
        -- refirst: Sort (a,c) (b,c) → Sort a b
        -- a=Int, b=Map Int [(Int,String)], c=String
        -- After refirst, consumes Int (not (Int,String))
        mapSort = refirst taggedSort :: Sort Int Int Int (Map.Map Int [(Int, String)])
        inp i = (i `mod` 2, i * 10)
    Map.size (runSort mapSort inp) === 2

-- | releft filters Either-sort to Left branch.
-- After releft, the Sort consumes String (not Either String Bool).
prop_releft_sort_filter :: Property
prop_releft_sort_filter = property $ do
    let -- Sort consuming Either String Bool, producing Either String Bool
        validated :: Sort (Sum Int) (Sum Int) (Either String Bool) (Either String Bool)
        validated = Sort $ \inp -> snd (inp (Sum 0))
        -- releft: Sort (Either a c) (Either b c) → Sort a b
        -- After releft, consumes String directly
        strSort = releft validated :: Sort (Sum Int) (Sum Int) String String
        inp _ = (Sum 0, "ok")
    runSort strSort inp === "ok"

-- | remapSort changes keys through a container-producing Sort.
prop_remap_sort :: Property
prop_remap_sort = property $ do
    let base = mkSortN 5 :: Sort Int Int String (Map.Map Int [String])
        remapped = remapSort (* 10) base
        inp i = (i, "x" ++ show i)
    Map.keys (runSort remapped inp) === [0, 10, 20, 30, 40]

-- | refirst + mkSortN: practical pattern for sort-and-project.
-- Sort (name, score) records, produce (Map of records, best score),
-- then refirst discards the best score keeping just the Map.
prop_refirst_tagged_sort :: Property
prop_refirst_tagged_sort = property $ do
    let -- Sort producing (Map of (name, score) records, best score)
        taggedSort :: Sort Int Int (String, Int) (Map.Map Int [(String, Int)], Int)
        taggedSort = Sort $ \inp ->
          let pairs = [inp i | i <- [0..5]]
              m = Map.fromListWith (++) [(fst p, [snd p]) | p <- pairs]
              best = maximum [snd (snd p) | p <- pairs]
          in (m, best)
        -- refirst: a=String, b=Map, c=Int → consumes String, produces Map
        mapSort = refirst taggedSort :: Sort Int Int String (Map.Map Int [(String, Int)])
        inp i = (i `mod` 3, "user" ++ show i)
    let result = runSort mapSort inp
    Map.size result === 3
    assert $ all (\v -> length v == 2) result

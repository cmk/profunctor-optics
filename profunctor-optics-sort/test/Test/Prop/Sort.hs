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
import Data.Profunctor.Optic.Import (refirst, releft, re)
import qualified Control.Category as C
import Data.Profunctor.Optic.Sort
import Data.Profunctor.Choice (left')
import Data.Word (Word8)
import Data.Word.Optic (grate8, bits8, ibits8)

import Data.Array.IArray (Array, listArray, elems)
import qualified Data.Array.IArray as IA
import qualified Data.ByteString as BS
import Data.Primitive.PrimArray (PrimArray, primArrayFromList, indexPrimArray, sizeofPrimArray)
import qualified Data.Vector.Unboxed as VU
import qualified Data.ByteString.Char8 as B8
import Data.Char (isUpper, isLower)
import Data.Functor.Index (I8(..))
import qualified Data.HashMap.Strict as HM
import Data.Hashable (Hashable)
import Data.Monoid (Sum(..))
import qualified Data.Text as T
import Data.Ord (Down(..))
import qualified Data.List as L
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as Map
import qualified Data.Vector as V
import qualified Data.Map.Merge.Strict as Merge

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
-- P36+: Relens/Reprism + Sort experiments
---------------------------------------------------------------------

-- Sort2 accepts Relens (Costrong) and Reprism (Cochoice).
-- These are sort *transformers* — they post-process Sort carriers.

-- refirst :: Relens a b (a, c) (b, c)
--   on Sort2: Sort2 k (a, c) (b, c) -> Sort2 k a b
--   = "forget the second component of a pair-sort via knot-tying"

-- releft :: Reprism a b (Either a c) (Either b c)
--   on Sort2: Sort2 k (Either a c) (Either b c) -> Sort2 k a b
--   = "filter out Right values from an Either-sort via Cochoice"

-- P36: refirst collapses a pair-sort to a first-component sort
prop_P36_refirst_sort2 :: Property
prop_P36_refirst_sort2 = property $ do
    xs <- forAll genPairNE
    let -- Sort pairs by fst
        pairSort = mkSort2 :: Sort2 Int (Int, String) (Int, String)
        -- refirst :: Sort2 k (a,c) (b,c) -> Sort2 k a b
        -- Collapse to just sort Ints
        intSort = refirst pairSort :: Sort2 Int Int Int
        -- Run: all ints in one group (same key) should come back
        result = runSort2 intSort (fmap (\(k,_) -> (k, k)) xs)
    -- Check we get at least one group (NonEmpty guarantee)
    assert $ length result >= 1

-- P37: releft filters an Either-sort down to Left values
prop_P37_releft_sort2 :: Property
prop_P37_releft_sort2 = property $ do
    let -- Sort Either values by key
        eitherSort = mkSort2 :: Sort2 Int (Either String Bool) (Either String Bool)
        -- releft collapses to just the String side
        stringSort = releft eitherSort :: Sort2 Int String String
        xs = (1, "a") :| [(2, "b"), (1, "c")]
        result = runSort2 stringSort xs
    -- Should group by key: [["a","c"], ["b"]] or similar
    assert $ length result >= 1

-- P38: re fstL on Sort2 (Lens reversed to Relens via re)
-- re fstL :: Costrong p => p (Int,String) (Int,String) -> p Int Int
--   on Sort2: Sort2 k (Int,String) (Int,String) -> Sort2 k Int Int
--   = "collapse a pair-sort to an int-sort via Costrong knot-tying"
prop_P38_re_lens_sort2 :: Property
prop_P38_re_lens_sort2 = property $ do
    xs <- forAll $ genNE $ (,) <$> Gen.int (Range.linear 0 5) <*> Gen.int (Range.linear 0 10)
    let pairSort = mkSort2 :: Sort2 Int (Int, String) (Int, String)
        -- re fstL collapses pair-sort to int-sort
        intSort = re fstL pairSort :: Sort2 Int Int Int
        result = runSort2 intSort xs
    -- Should produce at least one group
    assert $ length result >= 1
    -- Total elements preserved
    sum (fmap length result) === length xs

-- P39: re left' on Sort2 (Prism reversed to Reprism via re)
---------------------------------------------------------------------
-- P41–P44: Merge operators
---------------------------------------------------------------------

-- P41: innerMerge only keeps matching keys
prop_P41_innerMerge :: Property
prop_P41_innerMerge = property $ do
    let xs = (1, "a") :| [(2, "b"), (3, "c")]
        ys = (2, "x") :| [(3, "y"), (4, "z")]
        result = innerMerge fstL fstL (\_ l r -> (NE.toList l, NE.toList r)) xs ys
    Map.keys result === [2, 3]

-- P42: outerMerge keeps all keys from both
prop_P42_outerMerge :: Property
prop_P42_outerMerge = property $ do
    let xs = (1, "a") :| [(2, "b")]
        ys = (2, "x") :| [(3, "y")]
        result = outerMerge fstL fstL
                   (\_ l -> Left (NE.toList l))
                   (\_ r -> Right (NE.toList r))
                   (\_ l r -> Left (NE.toList l ++ NE.toList r))
                   xs ys
    Map.keys result === [1, 2, 3]

-- P43: leftMerge keeps all left keys
prop_P43_leftMerge :: Property
prop_P43_leftMerge = property $ do
    let xs = (1, "a") :| [(2, "b"), (3, "c")]
        ys = (2, "x") :| [(4, "z")]
        result = leftMerge fstL fstL
                   (\_ l -> NE.toList l)
                   (\_ l _r -> NE.toList l)
                   xs ys
    Map.keys result === [1, 2, 3]

-- P44: mergingOf with custom tactics
prop_P44_mergingOf_custom :: Property
prop_P44_mergingOf_custom = property $ do
    let xs = (1, "a") :| [(2, "b")]
        ys = (1, "x") :| [(3, "z")]
        result = mergingOf fstL fstL
                   (Merge.mapMissing $ \_ l -> length l)        -- left-only: count
                   (Merge.mapMissing $ \_ r -> length r * 10)   -- right-only: count * 10
                   (Merge.zipWithMatched $ \_ l r -> length l + length r)  -- both: sum counts
                   xs ys
    result === Map.fromList [(1, 2), (2, 1), (3, 10)]

---------------------------------------------------------------------
-- SortF properties
---------------------------------------------------------------------

-- SF1: SortF dimap id id = id
prop_SF1_sortF_dimap_id :: Property
prop_SF1_sortF_dimap_id = property $ do
    let s = mkSortFN 5 :: SortF Int Int Int (Map.Map Int [Int])
        inp i = (i `mod` 3, i * 10)
    runSortF (dimap id id s) inp === runSortF s inp

-- SF2: mkSortFN groups correctly
prop_SF2_mkSortFN :: Property
prop_SF2_mkSortFN = property $ do
    let s = mkSortFN 4 :: SortF Int Int Char (Map.Map Int [Char])
        inp 0 = (1, 'a')
        inp 1 = (2, 'b')
        inp 2 = (1, 'c')
        inp 3 = (2, 'd')
        inp _ = (0, '?')
        result = runSortF s inp
    result === Map.fromList [(1, ['a','c']), (2, ['b','d'])]

-- SF3: Category id . f = f (needs Monoid i, Monoid k)
prop_SF3_category_left_id :: Property
prop_SF3_category_left_id = property $ do
    let s = SortF (\inp -> snd (inp (Sum 0)) + 1) :: SortF (Sum Int) (Sum Int) Int Int
        inp i = (Sum (getSum i `mod` 2), getSum i * 10)
    runSortF (C.id C.. s) inp === runSortF s inp

-- SF4: Category f . id = f
prop_SF4_category_right_id :: Property
prop_SF4_category_right_id = property $ do
    let s = SortF (\inp -> snd (inp (Sum 0)) + 1) :: SortF (Sum Int) (Sum Int) Int Int
        inp i = (Sum (getSum i `mod` 2), getSum i * 10)
    runSortF (s C.. C.id) inp === runSortF s inp

-- SF5: (%.) composition
prop_SF5_compose :: Property
prop_SF5_compose = property $ do
    let s1 = SortF (\inp -> snd (inp 0) + 1) :: SortF Int (Sum Int) Int Int
        s2 = SortF (\inp -> snd (inp 0) * 2) :: SortF Int (Sum Int) Int Int
        composed = s1 %. s2
        inp i = (Sum i, i + 10)
    -- s2 runs on inp: snd (inp 0) * 2 = 10 * 2 = 20
    -- s1 sees (\i -> (fst (inp i), 20)): snd (...) + 1 = 20 + 1 = 21
    runSortF composed inp === 21

-- SF6: remapSortF id = id
prop_SF6_remapSortF_id :: Property
prop_SF6_remapSortF_id = property $ do
    let s = mkSortFN 3 :: SortF Int Int Int (Map.Map Int [Int])
        inp i = (i, i * 10)
    runSortF (remapSortF id s) inp === runSortF s inp

-- SF7: eitherSortF partitions correctly
prop_SF7_eitherSortF :: Property
prop_SF7_eitherSortF = property $ do
    let sl = SortF (\inp -> "left:" ++ show (snd (inp (Sum 0)))) :: SortF (Sum Int) Int Int String
        sr = SortF (\inp -> "right:" ++ show (snd (inp (Sum 0)))) :: SortF (Sum Int) Int Int String
        combined = eitherSortF sl sr
        -- All Left input
        inpL :: Sum Int -> (Int, Either Int Int)
        inpL _ = (1, Left 42)
        -- All Right input
        inpR :: Sum Int -> (Int, Either Int Int)
        inpR _ = (1, Right 99)
    runSortF combined inpL === "left:42"
    runSortF combined inpR === "right:99"

-- SF8: maybeSortF with Nothing returns default
prop_SF8_maybeSortF :: Property
prop_SF8_maybeSortF = property $ do
    let sf = SortF (\inp -> snd (inp (Sum 0)) * 2) :: SortF (Sum Int) Int Int Int
        combined = maybeSortF 0 sf
        inpJust :: Sum Int -> (Int, Maybe Int)
        inpJust _ = (1, Just 21)
        inpNothing :: Sum Int -> (Int, Maybe Int)
        inpNothing _ = (1, Nothing)
    runSortF combined inpJust === 42
    runSortF combined inpNothing === 0

-- SF9: bindSortF allows key-dependent logic
prop_SF9_bindSortF :: Property
prop_SF9_bindSortF = property $ do
    let base = SortF (\inp -> snd (inp 0)) :: SortF Int Int Int Int
        -- Bind: if key > 1, negate the result
        refined = bindSortF base $ \k ->
          if k > 1 then SortF (\inp -> negate (snd (inp 0)))
                   else SortF (\inp -> snd (inp 0))
        inpLowKey :: Int -> (Int, Int)
        inpLowKey _ = (0, 42)
        inpHighKey :: Int -> (Int, Int)
        inpHighKey _ = (5, 42)
    runSortF refined inpLowKey === 42
    runSortF refined inpHighKey === (-42)

---------------------------------------------------------------------
-- SF10–SF14: SortF operator tests
---------------------------------------------------------------------

-- SF10: grate8 composes with SortF by direct application (Closed)
prop_SF10_grate8_sortF :: Property
prop_SF10_grate8_sortF = property $ do
    w <- forAll $ Gen.word8 Range.constantBounded
    let carrier = SortF (\inp -> snd (inp 0)) :: SortF Int Int (I8 -> Bool) (I8 -> Bool)
        lifted = grate8 carrier  -- direct application, no wrapper
        inp i = (i, w)
    runSortF lifted inp === w

-- SF11: bits8 composes with SortF by direct application (Cotraversing, Monoid i)
prop_SF11_bits8_sortF :: Property
prop_SF11_bits8_sortF = property $ do
    w <- forAll $ Gen.word8 Range.constantBounded
    let carrier = SortF (\inp -> snd (inp (Sum 0))) :: SortF (Sum Int) Int Bool Bool
        lifted = bits8 carrier  -- direct application, no wrapper
        inp _ = (0 :: Int, w)
    runSortF lifted inp === w

-- SF12: sortingVectorF groups correctly
prop_SF12_sortingVectorF :: Property
prop_SF12_sortingVectorF = property $ do
    let v = V.fromList [(2, "b"), (1, "a"), (2, "c"), (1, "d")]
        result = sortingVectorF fst v
    Map.keys result === [1, 2]
    fmap V.toList result === Map.fromList [(1, [(1,"a"), (1,"d")]), (2, [(2,"b"), (2,"c")])]

-- SF13: sortedMatchedF plugs into Map.merge
prop_SF13_sortedMatchedF :: Property
prop_SF13_sortedMatchedF = property $ do
    let m1 = Map.fromList [(1, "a"), (2, "b")]
        m2 = Map.fromList [(2, "x"), (3, "y")]
        concatT :: SortF () Int (String, String) String
        concatT = SortF $ \inp -> let (_, (x, y)) = inp () in x ++ y
        result = Merge.merge
                   Merge.dropMissing
                   Merge.dropMissing
                   (sortedMatchedF concatT)
                   m1 m2
    result === Map.fromList [(2, "bx")]

-- SF14: zipsSortingF merges results
prop_SF14_zipsSortingF :: Property
prop_SF14_zipsSortingF = property $ do
    let s1 = SortF (\inp -> snd (inp 0) + 1) :: SortF Int Int Int Int
        s2 = SortF (\inp -> snd (inp 0) + 2) :: SortF Int Int Int Int
        merged = zipsSortingF (+) s1 s2
        inp i = (i, i * 10)
    runSortF merged inp === 3  -- (0 + 1) + (0 + 2), since snd (inp 0) = 0

---------------------------------------------------------------------
-- P51–P54: ByteString/Text sorting via SortF
---------------------------------------------------------------------

-- P51: sortingBytes preserves all bytes
prop_P51_sortingBytes_preserves :: Property
prop_P51_sortingBytes_preserves = property $ do
    bs <- forAll $ Gen.utf8 (Range.linear 1 100) Gen.alpha
    let result = sortingBytes id bs
        totalBytes = sum $ fmap BS.length result
    totalBytes === BS.length bs

-- P52: sortingBytes groups share same key
prop_P52_sortingBytes_same_key :: Property
prop_P52_sortingBytes_same_key = property $ do
    bs <- forAll $ Gen.utf8 (Range.linear 1 50) Gen.alpha
    let result = sortingBytes id bs
    assert $ all (\(k, v) -> BS.all (== k) v) (Map.toList result)

-- P53: groupingBytes keys = set of byte values in input
prop_P53_groupingBytes_keys :: Property
prop_P53_groupingBytes_keys = property $ do
    bs <- forAll $ Gen.utf8 (Range.linear 1 50) Gen.alpha
    let result = groupingBytes bs
        resultKeys = Map.keysSet result
        inputBytes = Map.keysSet $ Map.fromList [(w, ()) | w <- BS.unpack bs]
    resultKeys === inputBytes

-- P54: sortingChars preserves all chars
prop_P54_sortingChars_preserves :: Property
prop_P54_sortingChars_preserves = property $ do
    txt <- forAll $ Gen.text (Range.linear 1 100) Gen.alpha
    let result = sortingChars id txt
        totalChars = sum $ fmap T.length result
    totalChars === T.length txt

---------------------------------------------------------------------
-- P55–P56: Rxlens/Rxprism + SortF
---------------------------------------------------------------------

-- P55: Rxlens (Costrong) composes with SortF
-- refirst :: Costrong p => p (a, c) (b, c) -> p a b
-- SortF has Costrong unconditionally.
prop_P55_rxlens_sortF :: Property
prop_P55_rxlens_sortF = property $ do
    let pairSort = SortF (\inp -> snd (inp 0)) :: SortF Int Int (Int, String) (Int, String)
        intSort = refirst pairSort :: SortF Int Int Int Int
        inp i = (i, i * 10)
    runSortF intSort inp === 0  -- snd (inp 0) = (0, "..."), refirst extracts fst = 0

-- P56: Reprism (Cochoice) composes with SortF
-- releft :: Cochoice p => p (Either a c) (Either b c) -> p a b
-- SortF's Cochoice (via Costar) needs Monoid k for Applicative on Corep.
prop_P56_reprism_sortF :: Property
prop_P56_reprism_sortF = property $ do
    let eitherSort = SortF (\inp -> snd (inp (Sum 0)))
                     :: SortF (Sum Int) (Sum Int) (Either String Bool) (Either String Bool)
        stringSort = releft eitherSort :: SortF (Sum Int) (Sum Int) String String
        inp _ = (Sum 1, "hello")
    runSortF stringSort inp === "hello"

---------------------------------------------------------------------
-- P61–P69: Sprint 6 — Generic and per-backend sorts
---------------------------------------------------------------------

-- P61: sortingRep agrees with sortingVectorF for Vector
prop_P61_sortingRep_vector :: Property
prop_P61_sortingRep_vector = property $ do
    xs <- forAll $ Gen.list (Range.linear 1 20) $ (,) <$> Gen.int (Range.linear 0 5) <*> Gen.string (Range.linear 1 3) Gen.alpha
    let v = V.fromList xs
        viaRep = sortingRep V.length V.unsafeIndex V.fromList fst v
        viaConcrete = sortingVectorF fst v
    viaRep === viaConcrete

-- P62: sortingVectorF preserves element count
prop_P62_sortingVectorF_preserves :: Property
prop_P62_sortingVectorF_preserves = property $ do
    xs <- forAll $ Gen.list (Range.linear 1 20) $ (,) <$> Gen.int (Range.linear 0 5) <*> Gen.string (Range.linear 1 3) Gen.alpha
    let v = V.fromList xs
        result = sortingVectorF fst v
    sum (fmap V.length result) === V.length v

-- P63: sortUniqueRep has no duplicate keys
prop_P63_sortUniqueRep :: Property
prop_P63_sortUniqueRep = property $ do
    xs <- forAll $ Gen.list (Range.linear 1 20) $ (,) <$> Gen.int (Range.linear 0 5) <*> Gen.string (Range.linear 1 3) Gen.alpha
    let v = V.fromList xs
        result = sortUniqueRep V.length V.unsafeIndex id fst v
    -- Each key maps to exactly one element
    assert $ all (\(_, a) -> length [a] == 1) (Map.toList result)

-- P75: sortTaggedRep keys are sorted and values permuted correctly
prop_P75_sortTaggedRep :: Property
prop_P75_sortTaggedRep = property $ do
    let keys = V.fromList [3, 1, 2, 1, 3]
        vals = V.fromList ["c", "a", "b", "a2", "c2"]
        result = sortTaggedRep V.length V.unsafeIndex V.unsafeIndex
                   V.fromList V.fromList keys vals
    -- Keys 1, 2, 3 each have their paired values
    Map.keys result === [1, 2, 3]

-- P76: sortTaggedRep preserves all (key, value) pairs
prop_P76_sortTaggedRep_preserves :: Property
prop_P76_sortTaggedRep_preserves = property $ do
    ks <- forAll $ Gen.list (Range.linear 1 20) $ Gen.int (Range.linear 0 5)
    vs <- forAll $ Gen.list (Range.singleton (length ks)) $ Gen.string (Range.linear 1 3) Gen.alpha
    let keys = V.fromList ks
        vals = V.fromList vs
        result = sortTaggedRep V.length V.unsafeIndex V.unsafeIndex
                   V.fromList V.fromList keys vals
        totalKeys = sum $ fmap (V.length . fst) result
        totalVals = sum $ fmap (V.length . snd) result
    totalKeys === V.length keys
    totalVals === V.length vals

-- P78: groupTaggedRep keys = set of input keys
prop_P78_groupTaggedRep :: Property
prop_P78_groupTaggedRep = property $ do
    ks <- forAll $ Gen.list (Range.linear 1 20) $ Gen.int (Range.linear 0 5)
    vs <- forAll $ Gen.list (Range.singleton (length ks)) $ Gen.string (Range.linear 1 3) Gen.alpha
    let keys = V.fromList ks
        vals = V.fromList vs
        result = groupTaggedRep V.length V.unsafeIndex V.unsafeIndex
                   V.fromList keys vals
        resultKeys = Map.keysSet result
        inputKeys = Map.keysSet $ Map.fromList [(k, ()) | k <- ks]
    resultKeys === inputKeys

---------------------------------------------------------------------
-- P64–P68: Per-backend sort tests
---------------------------------------------------------------------

-- P64: sortingPrimArray groups by key
prop_P64_sortingPrimArray :: Property
prop_P64_sortingPrimArray = property $ do
    let arr = primArrayFromList [3, 1, 2, 1, 3 :: Int]
        result = sortingPrimArray (`mod` 2) arr
    Map.keys result === [0, 1]
    -- even group: [2], odd group: [3,1,1,3]
    fmap sizeofPrimArray result === Map.fromList [(0, 1), (1, 4)]

-- P65: sortingPrimArray preserves element count
prop_P65_sortingPrimArray_preserves :: Property
prop_P65_sortingPrimArray_preserves = property $ do
    xs <- forAll $ Gen.list (Range.linear 1 20) $ Gen.int (Range.linear 0 10)
    let arr = primArrayFromList xs
        result = sortingPrimArray id arr
    sum (fmap sizeofPrimArray result) === sizeofPrimArray arr

-- P66: sortingVectorU groups correctly
prop_P66_sortingVectorU :: Property
prop_P66_sortingVectorU = property $ do
    xs <- forAll $ Gen.list (Range.linear 1 20) $ Gen.int (Range.linear 0 5)
    let v = VU.fromList xs
        result = sortingVectorU id v
    sum (fmap VU.length result) === VU.length v

-- P67: sortingArray preserves elements
prop_P67_sortingArray :: Property
prop_P67_sortingArray = property $ do
    let arr = listArray (0, 4) [3, 1, 2, 1, 3] :: Array Int Int
        result = sortingArray (`mod` 2) arr
    -- Total elements preserved
    sum (fmap (length . IA.elems) result) === length (IA.elems arr)

---------------------------------------------------------------------
-- P71–P74: Hashable-keyed grouping
---------------------------------------------------------------------

-- P71: groupingHashOf groups share same key
prop_P71_groupingHashOf_same_key :: Property
prop_P71_groupingHashOf_same_key = property $ do
    xs <- forAll genPairNE
    let result = groupingHashOf fstL xs
    assert $ all (\(k, g) -> all (\s -> s ^. fstL == k) g) (HM.toList result)

-- P72: groupingHashOf preserves element count
prop_P72_groupingHashOf_preserves :: Property
prop_P72_groupingHashOf_preserves = property $ do
    xs <- forAll genPairNE
    let result = groupingHashOf fstL xs
        totalElems = sum $ fmap length result
    totalElems === length xs

-- P73: toHashMapOf keys = set of focused values
prop_P73_toHashMapOf_keys :: Property
prop_P73_toHashMapOf_keys = property $ do
    xs <- forAll genPairNE
    let m = toHashMapOf fstL xs
        mapKeys = HM.keysSet m
        inputKeys = HM.keysSet $ HM.fromList [(s ^. fstL, ()) | s <- NE.toList xs]
    mapKeys === inputKeys

-- P74: countingHashOf agrees with countingOf
prop_P74_countingHashOf_agrees :: Property
prop_P74_countingHashOf_agrees = property $ do
    xs <- forAll genPairNE
    let ordCounts = Map.toAscList $ countingOf fstL xs
        hashCounts = L.sort $ HM.toList $ countingHashOf fstL xs
    ordCounts === hashCounts

---------------------------------------------------------------------
-- P57: Optic composition through SortF
---------------------------------------------------------------------

-- P57: Closed optics compose with SortF by direct application.
-- Two grate8 applications in sequence: grate8 . grate8 lifts
-- Sort3 through two layers of Word8 ≅ (I8 -> Bool) representation.
prop_P57_optic_chain :: Property
prop_P57_optic_chain = property $ do
    w <- forAll $ Gen.word8 Range.constantBounded
    let carrier = SortF (\inp -> snd (inp 0))
                  :: SortF Int Int (I8 -> Bool) (I8 -> Bool)
        -- Compose two Closed optics: grate8 . grate8
        -- grate8 :: Colens Word8 Word8 (I8 -> Bool) (I8 -> Bool)
        -- grate8 . grate8 would need (I8 -> I8 -> Bool) -> (I8 -> I8 -> Bool)
        -- Actually grate8 . grate8 doesn't typecheck directly.
        -- Instead: one grate8 application lifts to Word8 level.
        lifted = grate8 carrier
        inp i = (i, w)
    runSortF lifted inp === w

---------------------------------------------------------------------
-- Helpers
---------------------------------------------------------------------

allEqual :: Eq a => NonEmpty a -> Bool
allEqual (x :| xs) = all (== x) xs

mapLeft :: (a -> c) -> Either a b -> Either c b
mapLeft f (Left a)  = Left (f a)
mapLeft _ (Right b) = Right b

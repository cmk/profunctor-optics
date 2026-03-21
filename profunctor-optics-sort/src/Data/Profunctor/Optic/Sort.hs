{-# LANGUAGE RankNTypes #-}
-- | Profunctor-optic interface to discrimination.
--
-- Operators (names containing @-ing@) take an optic as an argument.
-- The optic type determines which Sort variant is used as carrier:
--
-- * 'Lens' (Strong + Choice) → Sort1
-- * Sort2 reified (+ Costrong + Cochoice) → Sort2
-- * 'Colens' (Closed) → SortF
module Data.Profunctor.Optic.Sort
  ( -- * Reified optic types
    ASort1, ASort2

    -- * Core runners (carrier pattern)
  , builds1
  , builds2
  , buildsWith1

    -- * Sort1 operators (Lens, Strong + Choice)
  , sortingOf
  , sortingDescOf
  , groupingOf
  , nubbingOf

    -- * Sort1 container construction
  , toMapOf
  , toMapWithOf
  , countingOf

    -- * Sort2 operators (+ Costrong + Cochoice)
  , groupingBack
  , nubbingBack
  , groupingDescBack

    -- * SortF operators
  , zipsSortingF
  , sortingVectorF
  , sortingBytes
  , groupingBytes
  , sortingChars

    -- * SortF merge tactics
  , sortedMatchedF
  , sortedMissingF

    -- * Indexed sorting (key = index)
  , sortingIx
  , toMapIx

    -- * Post-sort folds
  , foldSorting
  , foldSorting1
  , mconcatSorting

    -- * Merge (Sort + containers merge)
  , mergingOf
  , innerMerge
  , outerMerge
  , leftMerge
  , rightMerge

    -- * Joins (by key extractor, not optic-based)
  , joiningOf
  , innerJoinOf
  , outerJoinOf
  , leftJoinOf
  , rightJoinOf
  ) where

import Data.List.NonEmpty (NonEmpty(..))
import Data.Ord (Down(..))
import Data.Word (Word8)
import qualified Data.ByteString as BS
import qualified Data.Text as T
import qualified Data.Vector as V
import Data.Profunctor
import Data.Profunctor.Optic.Types (Lens', Colens, Ixlens', Cotraversal)
import Data.Profunctor.Optic.View ((^.))

import Data.Profunctor.Sort

import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as Map
import qualified Data.Map.Merge.Strict as Merge

-- ===================================================================
-- Reified optic types
-- ===================================================================

type ASort1 k s t a b = Sort1 k a b -> Sort1 k s t
type ASort2 k s t a b = Sort2 k a b -> Sort2 k s t

-- ===================================================================
-- Core runners (carrier pattern)
-- ===================================================================

-- | Sort through a reified optic using a Sort1 carrier.
builds1 :: ASort1 k s t a b -> (s -> k) -> Sort1 k a b -> NonEmpty s -> [NonEmpty t]
builds1 o key carrier xs =
  runSort1 (o carrier) (fmap (\s -> (key s, s)) xs)

-- | Sort through a reified optic using a Sort2 carrier.
builds2 :: ASort2 k s t a b -> (s -> k) -> Sort2 k a b -> NonEmpty s -> NonEmpty [t]
builds2 o key carrier xs =
  runSort2 (o carrier) (fmap (\s -> (key s, s)) xs)

-- | Sort and transform through a reified optic.
buildsWith1 :: Ord k => ASort1 k s t a b -> (s -> k) -> (a -> b) -> NonEmpty s -> [NonEmpty t]
buildsWith1 o key f = builds1 o key (rmap f mkSort1)

-- ===================================================================
-- Sort1 operators (Lens = Strong + Choice)
-- ===================================================================

-- | Sort through a lens. The lens focuses on the sort key @a@
-- within @s@. @Ord a@ discriminates on it. Context is carried
-- through via Strong.
--
sortingOf :: Ord a
          => Lens' s a
          -> NonEmpty s -> [NonEmpty s]
sortingOf o xs =
  runSort1 (o mkSort1) (fmap (\s -> (s ^. o, s)) xs)

-- | Sort through a lens in descending order.
--
sortingDescOf :: Ord a
              => Lens' s a
              -> NonEmpty s -> [NonEmpty s]
sortingDescOf o xs =
  runSort1 (o (sortOn1 Down mkSort1)) (fmap (\s -> (s ^. o, s)) xs)

-- | Group through a lens (= 'sortingOf').
groupingOf :: Ord a
           => Lens' s a
           -> NonEmpty s -> [NonEmpty s]
groupingOf = sortingOf

-- | Deduplicate through a lens, keeping first per group.
nubbingOf :: Ord a
          => Lens' s a
          -> NonEmpty s -> [s]
nubbingOf o = map NE.head . sortingOf o

-- ===================================================================
-- Sort1 container construction
-- ===================================================================

-- | Sort through a lens and collect groups into a 'Map' keyed by the
-- focused value.
--
toMapOf :: Ord a
        => Lens' s a
        -> NonEmpty s -> Map.Map a (NonEmpty s)
toMapOf o xs =
  Map.fromList [(NE.head g ^. o, g) | g <- sortingOf o xs]

-- | Sort through a lens and build a 'Map' by applying a value
-- transform to each element, combining with @('<>')@.
--
toMapWithOf :: (Ord a, Semigroup v)
            => Lens' s a -> (s -> v)
            -> NonEmpty s -> Map.Map a v
toMapWithOf o f xs =
  Map.fromListWith (<>) [(s ^. o, f s) | s <- NE.toList xs]

-- | Count occurrences per key through a lens.
--
countingOf :: Ord a
           => Lens' s a
           -> NonEmpty s -> Map.Map a Int
countingOf o xs =
  Map.fromListWith (+) [(s ^. o, 1 :: Int) | s <- NE.toList xs]

-- ===================================================================
-- Sort2 operators (+ Costrong + Cochoice)
-- ===================================================================

-- | Group through a lens using Sort2. Guarantees ≥1 group.
-- Groups can be empty.
groupingBack :: Ord a
             => Lens' s a
             -> NonEmpty s -> NonEmpty [s]
groupingBack o xs =
  runSort2 (o mkSort2) (fmap (\s -> (s ^. o, s)) xs)

-- | Deduplicate through a lens using Sort2. Returns the head of
-- each group (or 'Nothing' for empty groups). Guarantees ≥1 result.
nubbingBack :: Ord a
            => Lens' s a
            -> NonEmpty s -> NonEmpty (Maybe s)
nubbingBack o = fmap listToMaybe . groupingBack o
  where listToMaybe []    = Nothing
        listToMaybe (x:_) = Just x

-- | Group through a lens in descending order using Sort2.
groupingDescBack :: Ord a
                 => Lens' s a
                 -> NonEmpty s -> NonEmpty [s]
groupingDescBack o xs =
  runSort2 (o (sortOn2 Down mkSort2)) (fmap (\s -> (s ^. o, s)) xs)

-- ===================================================================
-- Indexed sorting (key = index)
-- ===================================================================

-- | Sort via an 'Ixlens'': the index IS the discrimination key.
--
-- No separate key extractor needed. The carrier is
-- @rmap snd mkSort1 :: Sort1 k (k, a) a@ which matches
-- @Ix (Sort1 k) k a a@.
sortingIx :: Ord k
          => Ixlens' k s a
          -> NonEmpty (k, s)
          -> [NonEmpty s]
sortingIx o xs =
  let carrier = rmap snd mkSort1
  in  runSort1 (o carrier) (fmap (\(k, s) -> (k, (k, s))) xs)

-- | Sort via an indexed lens and collect groups into a 'Map'
-- keyed by the index.
toMapIx :: Ord k
        => Ixlens' k s a
        -> NonEmpty (k, s)
        -> Map.Map k (NonEmpty s)
toMapIx o xs =
  Map.fromList [(k, g) | g <- sortingIx o xs, let k = fst (NE.head pairs)]
  where pairs = fmap (\(k, s) -> (k, (k, s))) xs
-- TODO: this is not right — revisit when indexed operators are fleshed out

-- ===================================================================
-- SortF operators
-- ===================================================================

-- Note: Colens and Cotraversal optics compose with SortF by
-- direct application — no wrapper needed:
--
-- @
-- grate8 carrier  :: SortF I8 k Word8 Word8    -- Colens (Closed)
-- bits8  carrier  :: SortF I8 k Word8 Word8    -- Cotraversal (Monoid i)
-- @
--
-- The optic IS the composition. See grate8/bits8 docs in
-- profunctor-optics-strings.

-- | Merge two SortF results pointwise.
--
zipsSortingF :: (b -> b -> b) -> SortF i k a b -> SortF i k a b -> SortF i k a b
zipsSortingF f (SortF h1) (SortF h2) = SortF $ \inp -> f (h1 inp) (h2 inp)

-- | Sort a 'Vector' by key using SortF.
--
-- The vector is an @Int@-indexed representable container.
-- Groups positions by key via 'mkSortFN', producing a 'Map'
-- of vectors.
--
sortingVectorF :: Ord k
               => (a -> k)
               -> V.Vector a -> Map.Map k (V.Vector a)
sortingVectorF key v =
  let n = V.length v
      result = runSortF (mkSortFN n) (\i -> (key (v V.! i), v V.! i))
  in  fmap V.fromList result

-- | Sort a strict 'ByteString' by a key on each byte.
--
-- The ByteString is an @Int@-indexed representable container of
-- 'Word8' values. Groups bytes by key via 'mkSortFN', producing
-- a 'Map' of ByteStrings.
--
sortingBytes :: Ord k
             => (Word8 -> k)
             -> BS.ByteString -> Map.Map k BS.ByteString
sortingBytes key bs =
  let n = BS.length bs
      result = runSortF (mkSortFN n) (\i -> (key (BS.index bs i), BS.index bs i))
  in  fmap BS.pack result

-- | Group a strict 'ByteString' by byte value.
--
groupingBytes :: BS.ByteString -> Map.Map Word8 BS.ByteString
groupingBytes = sortingBytes id

-- | Sort a strict 'Text' by a key on each character.
--
-- The Text is an @Int@-indexed representable container of 'Char'
-- values. Groups characters by key via 'mkSortFN', producing
-- a 'Map' of Texts.
--
sortingChars :: Ord k
             => (Char -> k)
             -> T.Text -> Map.Map k T.Text
sortingChars key txt =
  let n = T.length txt
      result = runSortF (mkSortFN n) (\i -> (key (T.index txt i), T.index txt i))
  in  fmap T.pack result

-- | Construct a 'WhenMatched' merge tactic from a SortF.
--
-- Uses @i = ()@ (one position per key). The carrier calls
-- @inp ()@ to receive the matched pair.
--
sortedMatchedF :: SortF () k (x, y) z -> Merge.SimpleWhenMatched k x y z
sortedMatchedF (SortF h) = Merge.zipWithMatched $ \k x y ->
  h (const (k, (x, y)))

-- | Construct a 'WhenMissing' merge tactic from a SortF.
--
-- Uses @i = ()@ (one position per key). The carrier calls
-- @inp ()@ to receive the missing value.
--
sortedMissingF :: SortF () k x y -> Merge.SimpleWhenMissing k x y
sortedMissingF (SortF h) = Merge.mapMissing $ \k x ->
  h (const (k, x))

-- ===================================================================
-- Post-sort fold operators
-- ===================================================================

-- | Sort through a lens, then right-fold each group.
foldSorting :: Ord a
            => Lens' s a
            -> (s -> r -> r) -> r
            -> NonEmpty s -> [r]
foldSorting o g z xs =
  map (foldr g z . NE.toList) (sortingOf o xs)

-- | Sort through a lens, then reduce each group with a binary
-- function. Each group is non-empty, so no seed is needed.
foldSorting1 :: Ord a
             => Lens' s a
             -> (s -> s -> s)
             -> NonEmpty s -> [s]
foldSorting1 o f = map (foldr1 f) . sortingOf o

-- | Sort through a lens, then monoidal concat per group.
mconcatSorting :: (Ord a, Monoid m)
               => Lens' s a
               -> (s -> m)
               -> NonEmpty s -> [m]
mconcatSorting o g xs =
  map (foldMap g) (sortingOf o xs)

-- ===================================================================
-- Merge (Sort + containers merge)
-- ===================================================================

-- | Merge two collections through lenses using containers merge tactics.
--
-- Sorts both inputs by their respective lens focus, builds 'Map's of
-- groups, then merges using the provided 'WhenMissing' and 'WhenMatched'
-- tactics from @Data.Map.Merge.Strict@.
--
-- @
-- 'mergingOf' fstL sndL
--   'Merge.dropMissing'
--   'Merge.dropMissing'
--   ('Merge.zipWithMatched' $ \\_ xs ys -> (xs, ys))
--   leftInput rightInput
-- @
--
mergingOf :: Ord a
          => Lens' s a
          -> Lens' t a
          -> Merge.SimpleWhenMissing a (NonEmpty s) c
          -> Merge.SimpleWhenMissing a (NonEmpty t) c
          -> Merge.SimpleWhenMatched a (NonEmpty s) (NonEmpty t) c
          -> NonEmpty s -> NonEmpty t -> Map.Map a c
mergingOf lo ro wml wmr wm xs ys =
  Merge.merge wml wmr wm (toMapOf lo xs) (toMapOf ro ys)

-- | Inner merge: only keys present in both inputs.
--
-- @
-- 'innerMerge' fstL sndL f xs ys
-- @
--
innerMerge :: Ord a
           => Lens' s a
           -> Lens' t a
           -> (a -> NonEmpty s -> NonEmpty t -> c)
           -> NonEmpty s -> NonEmpty t -> Map.Map a c
innerMerge lo ro f =
  mergingOf lo ro Merge.dropMissing Merge.dropMissing (Merge.zipWithMatched f)

-- | Full outer merge: all keys from both inputs.
--
outerMerge :: Ord a
           => Lens' s a
           -> Lens' t a
           -> (a -> NonEmpty s -> c)
           -> (a -> NonEmpty t -> c)
           -> (a -> NonEmpty s -> NonEmpty t -> c)
           -> NonEmpty s -> NonEmpty t -> Map.Map a c
outerMerge lo ro fl fr fb =
  mergingOf lo ro (Merge.mapMissing fl) (Merge.mapMissing fr) (Merge.zipWithMatched fb)

-- | Left merge: all keys from left, matching keys from right.
--
leftMerge :: Ord a
          => Lens' s a
          -> Lens' t a
          -> (a -> NonEmpty s -> c)
          -> (a -> NonEmpty s -> NonEmpty t -> c)
          -> NonEmpty s -> NonEmpty t -> Map.Map a c
leftMerge lo ro fl fb =
  mergingOf lo ro (Merge.mapMissing fl) Merge.dropMissing (Merge.zipWithMatched fb)

-- | Right merge: all keys from right, matching keys from left.
--
rightMerge :: Ord a
           => Lens' s a
           -> Lens' t a
           -> (a -> NonEmpty t -> c)
           -> (a -> NonEmpty s -> NonEmpty t -> c)
           -> NonEmpty s -> NonEmpty t -> Map.Map a c
rightMerge lo ro fr fb =
  mergingOf lo ro Merge.dropMissing (Merge.mapMissing fr) (Merge.zipWithMatched fb)

-- ===================================================================
-- Joins (by key extractor, not optic-based)
-- ===================================================================
--
-- These are direct Sort1 combinators that do not take optics.
-- They use mkSort1 directly and partition via Either tagging.

-- | Full outer join by key extractors.
joiningOf :: Ord k
          => (a -> k) -> (b -> k)
          -> ([a] -> [b] -> c)
          -> [a] -> [b] -> [c]
joiningOf ak bk combine as bs =
  let tagged = [(ak a, Left a) | a <- as] ++ [(bk b, Right b) | b <- bs]
  in  case tagged of
        []   -> []
        t:ts -> map (combineGroup combine) (runSort1 mkSort1 (t :| ts))

-- | Inner join by key extractors.
innerJoinOf :: Ord k
            => (a -> k) -> (b -> k)
            -> (a -> b -> c)
            -> [a] -> [b] -> [c]
innerJoinOf ak bk f as bs =
  concatMap id $ joiningOf ak bk go as bs
  where
    go ap bp
      | null ap || null bp = []
      | otherwise          = [f a b | a <- ap, b <- bp]

-- | Full outer join by key extractors.
outerJoinOf :: Ord k
            => (a -> k) -> (b -> k)
            -> (a -> b -> c) -> (a -> c) -> (b -> c)
            -> [a] -> [b] -> [[c]]
outerJoinOf ak bk f ac bc as bs =
  joiningOf ak bk go as bs
  where
    go ap bp
      | null ap   = map bc bp
      | null bp   = map ac ap
      | otherwise = [f a b | a <- ap, b <- bp]

-- | Left outer join by key extractors.
leftJoinOf :: Ord k
           => (a -> k) -> (b -> k)
           -> (a -> b -> c) -> (a -> c)
           -> [a] -> [b] -> [[c]]
leftJoinOf ak bk f ac as bs =
  filter (not . null) $ joiningOf ak bk go as bs
  where
    go ap bp
      | null ap   = []
      | null bp   = map ac ap
      | otherwise = [f a b | a <- ap, b <- bp]

-- | Right outer join by key extractors.
rightJoinOf :: Ord k
            => (a -> k) -> (b -> k)
            -> (a -> b -> c) -> (b -> c)
            -> [a] -> [b] -> [[c]]
rightJoinOf ak bk f bc as bs =
  filter (not . null) $ joiningOf ak bk go as bs
  where
    go ap bp
      | null bp   = []
      | null ap   = map bc bp
      | otherwise = [f a b | a <- ap, b <- bp]

-- ===================================================================
-- Internal helpers
-- ===================================================================

combineGroup :: ([a] -> [b] -> c) -> NonEmpty (Either a b) -> c
combineGroup f grp =
  let (ls, rs) = partitionEithers (NE.toList grp)
  in  f ls rs

partitionEithers :: [Either a b] -> ([a], [b])
partitionEithers = foldr step ([], [])
  where
    step (Left a)  (ls, rs) = (a:ls, rs)
    step (Right b) (ls, rs) = (ls, b:rs)

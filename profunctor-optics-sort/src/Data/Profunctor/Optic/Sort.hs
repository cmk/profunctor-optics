{-# LANGUAGE RankNTypes #-}
-- | Profunctor-optic interface to discrimination.
--
-- Operators (names containing @-ing@) take an optic as an argument.
-- The optic type determines which Sort variant is used as carrier:
--
-- * 'Lens' (Strong + Choice) → Sort1
-- * Sort2 reified (+ Costrong + Cochoice) → Sort2
-- * 'Colens' (Closed) → Sort3
module Data.Profunctor.Optic.Sort
  ( -- * Sort1 operators (Lens)
    sortingOf
  , groupingOf
  , nubbingOf

    -- * Sort2 operators (Lens on Sort2)
  , groupingBack

    -- * Sort3 operators (Closed)
  , sortingUnder

    -- * Indexed sorting (key = index)
  , sortingIx

    -- * Joins (two-table, by key extractor)
  , joiningOf
  , innerJoinOf
  , outerJoinOf
  , leftJoinOf
  , rightJoinOf

    -- * Reified optic types
  , ASort1, ASort2

    -- * Build through a reified optic
  , builds1
  , builds2
  , buildsWith1

    -- * Post-sort fold operators
  , foldSorting
  , mconcatSorting
  , minimumSorting
  , maximumSorting
  ) where

import Data.List.NonEmpty (NonEmpty(..))
import Data.Profunctor
import Data.Profunctor.Optic.Types (Lens', Colens, Ixlens')
import Data.Profunctor.Optic.View ((^.))

import Data.Profunctor.Sort

import qualified Data.List.NonEmpty as NE

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
-- Sort2 operators (+ Costrong + Cochoice)
-- ===================================================================

-- | Group through a lens using Sort2. Guarantees ≥1 group.
-- Groups can be empty.
groupingBack :: Ord a
             => Lens' s a
             -> NonEmpty s -> NonEmpty [s]
groupingBack o xs =
  runSort2 (o mkSort2) (fmap (\s -> (s ^. o, s)) xs)

-- ===================================================================
-- Sort3 operators (Closed)
-- ===================================================================

-- | Sort under a 'Colens' / grate: lift a Sort3 through a Closed
-- optic to sort representable structures pointwise.
sortingUnder :: Colens s t a b
             -> Sort3 i j k a b -> Sort3 i j k s t
sortingUnder g = g

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

-- ===================================================================
-- Joins (two-table, through a Lens)
-- ===================================================================

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
-- Reified optic types
-- ===================================================================

type ASort1 k s t a b = Sort1 k a b -> Sort1 k s t
type ASort2 k s t a b = Sort2 k a b -> Sort2 k s t

-- ===================================================================
-- Build through a reified optic
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
-- Post-sort fold operators
-- ===================================================================

-- | Sort through a lens, then right-fold each group.
foldSorting :: Ord a
            => Lens' s a
            -> (s -> r -> r) -> r
            -> NonEmpty s -> [r]
foldSorting o g z xs =
  map (foldr g z . NE.toList) (sortingOf o xs)

-- | Sort through a lens, then monoidal concat per group.
mconcatSorting :: (Ord a, Monoid m)
               => Lens' s a
               -> (s -> m)
               -> NonEmpty s -> [m]
mconcatSorting o g xs =
  map (foldMap g) (sortingOf o xs)

-- | Sort through a lens, then minimum per group.
minimumSorting :: (Ord a, Ord s)
               => Lens' s a
               -> NonEmpty s -> [s]
minimumSorting o xs =
  map minimum (sortingOf o xs)

-- | Sort through a lens, then maximum per group.
maximumSorting :: (Ord a, Ord s)
               => Lens' s a
               -> NonEmpty s -> [s]
maximumSorting o xs =
  map maximum (sortingOf o xs)

-- ===================================================================
-- Helpers
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

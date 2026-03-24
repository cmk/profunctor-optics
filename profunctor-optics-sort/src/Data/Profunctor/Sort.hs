{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TypeFamilies #-}
-- | Profunctor sort with separated key, input, and output parameters.
--
-- Three families:
--
-- * @Sort i k a b = (i -> (k, a)) -> b@ — the indexed Fmt.
--   Costar-shaped, derives all instances via @Costar (Compose ((->) i) ((,) k))@.
--   @Fmt m a b = Sort m () a b@.
-- * @Sort1 k a b = NonEmpty (k, a) -> [NonEmpty b]@ — non-empty in, list out (can fail).
-- * @Sort2 k a b = NonEmpty (k, a) -> NonEmpty [b]@ — non-empty in, ≥1 group, groups can be empty.
--
-- === Instance summary
--
-- @
--                Profunctor  Strong  Choice    Closed  Costrong  Cochoice  Cosieve  Corepresentable  Category
-- Sort  i k        ✓                ✓(Mon i)    ✓       ✓         ✓         ✓           ✓          ✓(Mon i,k)
-- Sort1  k          ✓          ✓       ✓
-- Sort2  k          ✓          ✓       ✓               ✓         ✓
-- @
--
-- Sort and Sort1 are complementary: Sort gets Closed (representable,
-- total), Sort1 gets Strong + Choice (concrete elements, can fail).
-- Sort2 sits between on the list-based side.
--
-- The failure\/totality axis IS the Strong-vs-Closed axis:
--
-- * Lists can be empty (failure) → elements accessible → Strong + Choice
-- * Functions are total (no failure) → elements hidden → Closed
module Data.Profunctor.Sort
  ( -- * Sort (re-exported from profunctor-optics core)
    Sort(..)
  , runSort
  , (%.)
  , bindSort
  , catSort
  , sortC
  , remapSort
  , eitherSort
  , maybeSort
  , zipsSorting

    -- * Sort carriers (Ord)
  , mkSort
  , mkSortN

    -- * Sort carriers (Hashable)
  , mkSortH
  , mkSortNH

    -- * Sort1 (non-empty in, can fail)
  , Sort1(..)
  , mkSort1
  , sortOn1

    -- * Sort2 (non-empty in, ≥1 group, groups can be empty)
  , Sort2(..)
  , mkSort2
  , sortOn2

  ) where

import Control.Arrow (second)
import Data.Either (lefts, rights)
import Data.Hashable (Hashable)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Profunctor
import Data.Profunctor.Optic.Sort (Sort(..), runSort, (%.), bindSort, catSort, sortC, remapSort, eitherSort, maybeSort, zipsSorting)

import Data.Functor.Coapply (Coapply(..))

import qualified Data.List.NonEmpty as NE
import qualified Data.HashMap.Strict as HM
import qualified Data.Map.Strict as Map

-- Sort type, instances, and combinators are re-exported from
-- Data.Profunctor.Optic.Carrier (profunctor-optics core).

---------------------------------------------------------------------
-- Sort carriers
---------------------------------------------------------------------

-- | Identity carrier for finite index types.
-- Groups by key, producing a 'Map' of toListOf.
--
-- Note: the lazy @(,)@ in @Sort@'s type is needed for DerivingVia.
-- Strictness is applied here at the carrier level: keys and values
-- are forced when building the Map.
mkSort :: (Bounded i, Enum i, Ord k) => Sort i k a (Map.Map k [a])
mkSort = Sort $ \inp ->
  Map.fromListWith (flip (++)) [ ki `seq` a `seq` (ki, [a])
                                | i <- [minBound..maxBound]
                                , let (ki, a) = inp i ]

-- | Identity carrier for Int-indexed containers of known size.
mkSortN :: Ord k => Int -> Sort Int k a (Map.Map k [a])
mkSortN n = Sort $ \inp ->
  Map.fromListWith (flip (++)) [ ki `seq` a `seq` (ki, [a])
                                | i <- [0..n-1]
                                , let (ki, a) = inp i ]

-- | Hashable carrier for finite index types.
-- Groups by key, producing a 'HashMap' of toListOf.
mkSortH :: (Bounded i, Enum i, Hashable k, Eq k) => Sort i k a (HM.HashMap k [a])
mkSortH = Sort $ \inp ->
  HM.fromListWith (flip (++)) [ ki `seq` a `seq` (ki, [a])
                                | i <- [minBound..maxBound]
                                , let (ki, a) = inp i ]

-- | Hashable carrier for Int-indexed containers of known size.
mkSortNH :: (Hashable k, Eq k) => Int -> Sort Int k a (HM.HashMap k [a])
mkSortNH n = Sort $ \inp ->
  HM.fromListWith (flip (++)) [ ki `seq` a `seq` (ki, [a])
                                | i <- [0..n-1]
                                , let (ki, a) = inp i ]

-- runSort is re-exported from Data.Profunctor.Optic.Carrier.

-- ===================================================================
--  Sort1 — NonEmpty (k, a) -> [NonEmpty b]
-- ===================================================================

-- | Non-empty input, possibly-empty output. Can fail (empty output
-- = no groups). Profunctor, Strong, Choice are total.
newtype Sort1 k a b = Sort1 { runSort1 :: NonEmpty (k, a) -> [NonEmpty b] }

-- | Group by key (Ord). Groups in ascending key order.
mkSort1 :: Ord k => Sort1 k a a
mkSort1 = Sort1 $ \pairs ->
  let mp = Map.fromListWith (\new old -> old <> new)
             [(k, a :| []) | (k, a) <- NE.toList pairs]
  in  Map.elems mp

-- | Re-key by a projection.
sortOn1 :: (k' -> k) -> Sort1 k a b -> Sort1 k' a b
sortOn1 f (Sort1 h) = Sort1 $ h . fmap (\(k', a) -> (f k', a))

instance Profunctor (Sort1 k) where
  dimap f g (Sort1 h) = Sort1 $ map (fmap g) . h . fmap (second f)
  lmap f (Sort1 h) = Sort1 $ h . fmap (second f)
  rmap g (Sort1 h) = Sort1 $ map (fmap g) . h

-- | Total: context extracted from 'NE.head'.
instance Strong (Sort1 k) where
  first' (Sort1 h) = Sort1 $ \pairs ->
    let c = snd $ snd $ NE.head pairs
    in  map (fmap (, c)) (h (fmap (\(k, (a, _)) -> (k, a)) pairs))
  second' (Sort1 h) = Sort1 $ \pairs ->
    let c = fst $ snd $ NE.head pairs
    in  map (fmap (c,)) (h (fmap (\(k, (_, a)) -> (k, a)) pairs))

-- | Total: partition via 'Coapply' 'NonEmpty'.
instance Choice (Sort1 k) where
  left' (Sort1 h) = Sort1 $ \pairs ->
    case coapply (fmap classify pairs) of
      Left  cs -> [Right (NE.head cs) :| []]
      Right ks -> map (fmap Left) (h ks)
    where
      classify (k, Left a)  = Right (k, a)
      classify (_, Right c) = Left c
  right' (Sort1 h) = Sort1 $ \pairs ->
    case coapply (fmap classify pairs) of
      Left  cs -> [Left (NE.head cs) :| []]
      Right ks -> map (fmap Right) (h ks)
    where
      classify (k, Right a) = Right (k, a)
      classify (_, Left c)  = Left c

-- ===================================================================
--  Sort2 — NonEmpty (k, a) -> NonEmpty [b]
-- ===================================================================

-- | Non-empty input, at least one group, groups can be empty.
--
-- Outer 'NonEmpty' guarantees Costrong (always a head to extract
-- feedback from). Inner @[b]@ (not @NonEmpty b@) allows Cochoice
-- to filter via 'lefts'/'rights' without ⊥ — empty groups are
-- representable.
newtype Sort2 k a b = Sort2 { runSort2 :: NonEmpty (k, a) -> NonEmpty [b] }

-- | Group by key (Ord). Groups in ascending key order.
mkSort2 :: Ord k => Sort2 k a a
mkSort2 = Sort2 $ \pairs ->
  let mp = Map.fromListWith (++) [(k, [a]) | (k, a) <- NE.toList pairs]
  in  case Map.elems mp of
        []   -> [] :| []  -- impossible for NonEmpty input, but safe
        g:gs -> g :| gs

-- | Re-key by a projection.
sortOn2 :: (k' -> k) -> Sort2 k a b -> Sort2 k' a b
sortOn2 f (Sort2 h) = Sort2 $ h . fmap (\(k', a) -> (f k', a))

instance Profunctor (Sort2 k) where
  dimap f g (Sort2 h) = Sort2 $ fmap (map g) . h . fmap (second f)
  lmap f (Sort2 h) = Sort2 $ h . fmap (second f)
  rmap g (Sort2 h) = Sort2 $ fmap (map g) . h

-- | Total: context extracted from 'NE.head'.
instance Strong (Sort2 k) where
  first' (Sort2 h) = Sort2 $ \pairs ->
    let c = snd $ snd $ NE.head pairs
    in  fmap (map (, c)) (h (fmap (\(k, (a, _)) -> (k, a)) pairs))
  second' (Sort2 h) = Sort2 $ \pairs ->
    let c = fst $ snd $ NE.head pairs
    in  fmap (map (c,)) (h (fmap (\(k, (_, a)) -> (k, a)) pairs))

-- | Total: partition via 'Coapply' 'NonEmpty'.
instance Choice (Sort2 k) where
  left' (Sort2 h) = Sort2 $ \pairs ->
    case coapply (fmap classify pairs) of
      Left  cs -> [Right (NE.head cs)] :| []
      Right ks -> fmap (map Left) (h ks)
    where
      classify (k, Left a)  = Right (k, a)
      classify (_, Right c) = Left c
  right' (Sort2 h) = Sort2 $ \pairs ->
    case coapply (fmap classify pairs) of
      Left  cs -> [Left (NE.head cs)] :| []
      Right ks -> fmap (map Right) (h ks)
    where
      classify (k, Right a) = Right (k, a)
      classify (_, Left c)  = Left c

-- | Total: knot-tying. Outer 'NonEmpty' guarantees a head group
-- for extracting the fed-back value.
instance Costrong (Sort2 k) where
  unfirst (Sort2 h) = Sort2 $ \pairs ->
    let groups = h (fmap (\(k, a) -> (k, (a, d))) pairs)
        d = snd $ head $ NE.head groups
    in  fmap (map fst) groups
  unsecond (Sort2 h) = Sort2 $ \pairs ->
    let groups = h (fmap (\(k, a) -> (k, (d, a))) pairs)
        d = fst $ head $ NE.head groups
    in  fmap (map snd) groups

-- | Total: filter via 'lefts'/'rights'. Empty groups are
-- representable in @[b]@, so no ⊥.
instance Cochoice (Sort2 k) where
  unleft (Sort2 h) = Sort2 $ \pairs -> go (fmap (second Left) pairs)
    where
      go pairs' = case NE.head (h pairs') of
        (Left _ : _) -> fmap lefts (h pairs')
        _            -> case rights (NE.head (h pairs')) of
          d:_ -> go (fmap (\(k, _) -> (k, Right d)) pairs')
          []  -> fmap lefts (h pairs')  -- all empty: done
  unright (Sort2 h) = Sort2 $ \pairs -> go (fmap (second Right) pairs)
    where
      go pairs' = case NE.head (h pairs') of
        (Right _ : _) -> fmap rights (h pairs')
        _             -> case lefts (NE.head (h pairs')) of
          d:_ -> go (fmap (\(k, _) -> (k, Left d)) pairs')
          []  -> fmap rights (h pairs')  -- all empty: done


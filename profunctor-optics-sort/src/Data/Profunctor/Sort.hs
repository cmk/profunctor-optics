{-# LANGUAGE TypeFamilies #-}
-- | Profunctor sort with separated key, input, and output parameters.
--
-- Three variants exploring the design space:
--
-- * @Sort1 k a b = NonEmpty (k, a) -> [NonEmpty b]@    — non-empty in, list out (can fail)
-- * @Sort2 k a b = NonEmpty (k, a) -> NonEmpty [b]@    — non-empty in, ≥1 group (groups can be empty)
-- * @Sort3 i j k a b = (i -> (k, a)) -> j -> k -> b@  — representable in, representable out
--
-- @k@ is the discrimination key (not a profunctor variable).
-- All are @Bistar f g a b = f a -> g b@ shaped — simultaneously
-- Star-like (structured output) and Costar-like (structured input).
-- Instances are hand-rolled.
--
-- === Instance summary (all total, no bottoms)
--
-- @
--                Profunctor  Strong  Choice  Closed  Costrong  Cochoice
-- Sort1  k          ✓          ✓       ✓
-- Sort2  k          ✓          ✓       ✓               ✓         ✓
-- Sort3  i j k      ✓                          ✓       ✓
-- @
--
-- Sort1 and Sort3 are complementary: Sort1 gets Strong + Choice
-- (concrete elements, can fail), Sort3 gets Closed (representable,
-- total). Sort2 sits between: ≥1 group guarantees Costrong, and
-- inner @[b]@ (not @NonEmpty b@) allows Cochoice to filter without ⊥.
--
-- The failure\/totality axis IS the Strong-vs-Closed axis:
--
-- * Lists can be empty (failure) → elements accessible → Strong + Choice
-- * Functions are total (no failure) → elements hidden → Closed
module Data.Profunctor.Sort
  ( -- * Sort1 (non-empty in, can fail)
    Sort1(..)
  , mkSort1
  , sortOn1

    -- * Sort2 (non-empty in, ≥1 group, groups can be empty)
  , Sort2(..)
  , mkSort2
  , sortOn2

    -- * Sort3 (representable in, representable out)
  , Sort3(..)
  ) where

import Control.Arrow (second)
import Data.Either (lefts, rights)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Profunctor

import Data.Functor.Coapply (Coapply(..))

import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as Map

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

-- ===================================================================
--  Sort3 — (i -> (k, a)) -> j -> k -> b
-- ===================================================================

-- | Representable-input, representable-output sort.
--
-- Both sides are function types. The output is indexed by group
-- position @j@ and key @k@, making it a coindexed optic carrier:
--
-- @
-- Cxtraversal k s t a b ≅ (f a -> k -> b) -> f s -> t
-- Sort3 i j k a b       ≅ (i -> (k, a)) -> j -> k -> b
-- @
--
-- Representable encoding hides elements behind @(i ->)@, blocking
-- Strong (can't extract context) and Choice (can't partition).
-- But @(->) j . (->) k@ on the output is Distributive, recovering
-- Closed (which the list-based variants lost).
newtype Sort3 i j k a b = Sort3 { runSort3 :: (i -> (k, a)) -> j -> k -> b }

instance Profunctor (Sort3 i j k) where
  dimap f g (Sort3 h) = Sort3 $ \inp j k ->
    g (h (\i -> second f (inp i)) j k)
  lmap f (Sort3 h) = Sort3 $ \inp j k ->
    h (\i -> second f (inp i)) j k
  rmap g (Sort3 h) = Sort3 $ \inp j k ->
    g (h inp j k)

-- | Total: both sides are functions, so @(x ->)@ distributes freely.
instance Closed (Sort3 i j k) where
  closed (Sort3 h) = Sort3 $ \inp j k x ->
    h (\i -> let (ki, xa) = inp i in (ki, xa x)) j k

-- | Total: knot-tying.
instance Costrong (Sort3 i j k) where
  unfirst (Sort3 h) = Sort3 $ \inp j k ->
    let (b, d) = h (\i -> let (ki, a) = inp i in (ki, (a, d))) j k
    in  b
  unsecond (Sort3 h) = Sort3 $ \inp j k ->
    let (d, b) = h (\i -> let (ki, a) = inp i in (ki, (d, a))) j k
    in  b

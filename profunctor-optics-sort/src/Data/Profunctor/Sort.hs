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
--                Profunctor  Strong  Choice  Closed  Costrong  Cochoice  Cosieve  Corepresentable
-- Sort1  k          ✓          ✓       ✓
-- Sort2  k          ✓          ✓       ✓               ✓         ✓
-- Sort3  i j k      ✓                          ✓       ✓                   ✓           ✓
-- @
--
-- Additionally, @Sort3Corep i j k@ has 'Coapply' and 'Coapplicative'
-- when @'Monoid' i@, making @Sort3@ satisfy
-- 'Data.Profunctor.Optic.Types.Cotraversing' in that case.
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

    -- * Sort3 corepresentation
  , Sort3Corep(..)

    -- * Sort3 carriers
  , mkSort3
  , sortOn3
  ) where

import Control.Arrow (first, second)
import Control.Coapplicative (Coapplicative(..))
import Data.Either (lefts, rights)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Profunctor
import Data.Profunctor.Rep (Corepresentable(..))
import Data.Profunctor.Sieve (Cosieve(..))

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
-- @
-- Sort3 i j k a b = (i -> (k, a)) -> j -> k -> b
-- @
--
-- *  @i@ — index into the input collection (element position)
-- *  @k@ — discrimination key (groups elements, shared across input and output)
-- *  @j@ — index within a group (position among elements sharing key @k@)
--
-- The output @j -> k -> b@ is the representable encoding of @[[b]]@
-- (outer list keyed by @k@, inner list indexed by @j@). This makes
-- it a coindexed optic carrier:
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
-- | Note: @Sort3 i j k a b ≅ Costar (Sort3Corep i j k) a b@, but
-- 'DerivingVia' cannot be used because the isomorphism is not
-- representational (it requires packing\/unpacking @j@ and @k@ into
-- the 'Sort3Corep' constructor).
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

instance Cosieve (Sort3 i j k) (Sort3Corep i j k) where
  cosieve (Sort3 h) (Sort3Corep ika j kv) = h ika j kv

instance Corepresentable (Sort3 i j k) where
  type Corep (Sort3 i j k) = Sort3Corep i j k
  cotabulate f = Sort3 $ \ika j kv -> f (Sort3Corep ika j kv)

-- ===================================================================
--  Sort3Corep — corepresentation of Sort3
-- ===================================================================

-- | Corepresentation of 'Sort3'. Bundles a tabulated input
-- @(i -> (k, a))@ with a group position @j@ and key @k@.
--
-- Unconditionally 'Functor'. With @'Monoid' i@, also 'Coapply' and
-- 'Coapplicative' (sampling at 'mempty', mirroring the @(->) r@
-- instance from @coapplicative@). This makes 'Sort3' satisfy
-- 'Data.Profunctor.Optic.Types.Cotraversing' when @i@ is a 'Monoid'.
data Sort3Corep i j k a = Sort3Corep (i -> (k, a)) j k

instance Functor (Sort3Corep i j k) where
  fmap f (Sort3Corep ika j kv) = Sort3Corep (second f . ika) j kv

-- | Sample at 'mempty' to decide the branch, mirroring the @(->) r@
-- instance. Values at other positions that disagree with 'mempty' are
-- defaulted to the sampled value.
instance Monoid i => Coapply (Sort3Corep i j k) where
  coapply (Sort3Corep ika j kv) = case snd (ika mempty) of
    Left a0  -> Left  (Sort3Corep (\i -> second (either id (const a0)) (ika i)) j kv)
    Right b0 -> Right (Sort3Corep (\i -> second (either (const b0) id) (ika i)) j kv)

instance Monoid i => Coapplicative (Sort3Corep i j k) where
  copure (Sort3Corep ika _ _) = snd (ika mempty)

-- ===================================================================
--  Sort3 carriers
-- ===================================================================

-- | Identity Sort3 carrier for finite index types.
--
-- Enumerates all input positions @[minBound..maxBound]@, groups
-- them by key (via 'Ord' on @k@), and produces a lookup by key
-- @k@ and within-group position @j@. Out-of-bounds @j@ wraps
-- modularly within the group.
--
-- This is the Sort3 analogue of 'mkSort1' / 'mkSort2'.
--
mkSort3 :: (Bounded i, Enum i, Ord k) => Sort3 i Int k a a
mkSort3 = Sort3 $ \inp j k ->
  let pairs = [(ki, (i, a)) | i <- [minBound..maxBound], let (ki, a) = inp i]
      grouped = Map.fromListWith (++) [(ki, [ia]) | (ki, ia) <- pairs]
      lookupAt kv idx = case Map.lookup kv grouped of
        Nothing -> snd $ snd $ head pairs  -- fallback: shouldn't happen for valid k
        Just ias -> let n = length ias
                    in  snd (ias !! (idx `mod` n))
  in  lookupAt k j

-- | Re-key a Sort3 carrier by a projection (applied to input keys
-- and output key lookups).
sortOn3 :: (k' -> k) -> Sort3 i j k a b -> Sort3 i j k' a b
sortOn3 f (Sort3 h) = Sort3 $ \inp j k' ->
  h (\i -> first f (inp i)) j (f k')

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

    -- * Sort composition
  , (%.)
  , bindSort
  , catSort

    -- * Sort construction
  , sortC
  , remapSort

    -- * Sort sum-type combinators
  , eitherSort
  , maybeSort

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

import Control.Arrow (first, second)
import Data.Either (lefts, rights)
import Data.Hashable (Hashable)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Profunctor
import Data.Profunctor.Optic.Carrier (Sort(..), runSort)

import Data.Functor.Coapply (Coapply(..))

import qualified Control.Category as C
import qualified Data.List.NonEmpty as NE
import qualified Data.HashMap.Strict as HM
import qualified Data.Map.Strict as Map

-- Sort type and instances are re-exported from
-- Data.Profunctor.Optic.Carrier (profunctor-optics core).

---------------------------------------------------------------------
-- Sort composition
---------------------------------------------------------------------

-- | Indexed bind: inspect the key at each position and choose
-- a continuation.
--
-- Unlike Fmt's @bind@ (which sees one monoid value), this is
-- position-dependent: the callback @f@ receives the key at
-- position @i@, chooses a Sort, and runs it on the same input.
--
-- @
-- 'bindSort' m f = Sort $ \\inp ->
--   unSort m (\\i -> let (k, _) = inp i in (k, 'unSort' (f k) inp))
-- @
--
{-# INLINE bindSort #-}
bindSort :: Sort i k a b -> (k -> Sort i k a' a) -> Sort i k a' b
bindSort (Sort m) f = Sort $ \inp ->
  m (\i -> let (k, _) = inp i in (k, unSort (f k) inp))

-- | Pipeline two Sort passes.
--
-- @f %. g@ runs @g@ on the full input to produce a single @b@,
-- then @f@ sees that @b@ at every position, paired with the
-- original keys (unchanged). The key @k@ is threaded through,
-- not accumulated — no 'Semigroup' constraint needed.
--
-- @
-- (f '%. g) '%.' h = f '%. (g '%. h)
-- @
--
infixr 9 %.
{-# INLINE (%.) #-}
(%.) :: Sort i k b c -> Sort i k a b -> Sort i k a c
Sort f %. Sort g = Sort $ \inp ->
  f (\i -> (fst (inp i), g inp))

-- | Fold multiple Sort passes via '%.'.
--
-- Analogous to Fmt's @cat@. Requires 'Monoid' @i@ and 'Monoid' @k@
-- for @Category@ 'id' (the seed of the fold).
--
{-# INLINE catSort #-}
catSort :: (Monoid i, Foldable f) => f (Sort i k a a) -> Sort i k a a
catSort = foldr (%.) C.id

---------------------------------------------------------------------
-- Sort construction
---------------------------------------------------------------------

-- | Constant: embed a key-value pair.
--
-- Analogous to Fmt's @fmt@.
{-# INLINE sortC #-}
sortC :: (k, a) -> Sort i k a (k, a)
sortC ka = Sort $ const ka

-- Note: Fmt's @fmt1 :: (a -> m) -> Fmt1 m s a@ doesn't translate to
-- Sort. In Fmt, @m@ is both the index and the monoid — the value
-- @a@ flows through the same channel as the accumulator. In Sort,
-- @i@ (index) and @k@ (key) are separated, so there's no single
-- @(a -> k)@ that serves as both \"extract key\" and \"provide value\".
-- Use 'sortC' for constants or 'mkSort'/'mkSortN' for carriers.

-- | Remap keys. @remapSort f@ transforms a @Sort@ that groups
-- by @k2@ into one that groups by @k1@, applying @f@ to map
-- keys from @k1@ to @k2@ in the input.
--
-- Analogous to Fmt's @refmt@.
{-# INLINE remapSort #-}
remapSort :: (k1 -> k2) -> Sort i k2 a b -> Sort i k1 a b
remapSort f (Sort g) = Sort $ \inp -> g (first f . inp)

---------------------------------------------------------------------
-- Sort sum-type combinators
---------------------------------------------------------------------

-- | Sort an Either: apply left sort to Lefts, right sort to Rights.
-- Samples at 'mempty' to decide the branch.
--
-- Analogous to Fmt's @either1@.
{-# INLINE eitherSort #-}
eitherSort :: Monoid i => Sort i k a c -> Sort i k b c -> Sort i k (Either a b) c
eitherSort (Sort l) (Sort r) = Sort $ \inp ->
  case snd (inp mempty) of
    Left a0  -> l (\i -> second (either id (const a0)) (inp i))
    Right b0 -> r (\i -> second (either (const b0) id) (inp i))

-- | Sort a Maybe: apply sort to Justs, use default for Nothings.
-- Samples at 'mempty' to decide.
--
-- Analogous to Fmt's @maybe1@.
{-# INLINE maybeSort #-}
maybeSort :: Monoid i => c -> Sort i k a c -> Sort i k (Maybe a) c
maybeSort def (Sort f) = Sort $ \inp ->
  case snd (inp mempty) of
    Nothing -> def
    Just a0 -> f (\i -> second (maybe a0 id) (inp i))

---------------------------------------------------------------------
-- Sort carriers
---------------------------------------------------------------------

-- | Identity carrier for finite index types.
-- Groups by key, producing a 'Map' of lists.
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
-- Groups by key, producing a 'HashMap' of lists.
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


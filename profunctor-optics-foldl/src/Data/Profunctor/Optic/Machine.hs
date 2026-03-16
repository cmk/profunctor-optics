{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Machine (
    -- * Types
    Moore, Mealy
  , Moore', Mealy'
    -- * Moore
  , moore
  , listing
  , foldingr
  , foldingr'
  , foldingl
  , foldingl'
  , foldingrM
  , foldinglM
  , traversing_
  , mappingM_
  , foldMapping
    -- * Mealy
  , mealy
  , listing1
  , foldingr1
  , foldingl1
  , foldingrM1
  , foldinglM1
  , traversing1_
  , foldMapping1
    -- * Optics
  , head1
  , last1
  , projected
  , minimized
  , maximized
  , minimizedDef
  , maximizedDef
  , minimizedBy
  , maximizedBy
  , minimizedByDef
  , maximizedByDef
  , foundDef
    -- * Operators
  , listl
  , listl1
  , steps
  , buildl
  , buildsl
  , buildl1
  , buildsl1
  , postscanl
  , postscansl
  , mconcats
  , sconcats
  , minimizes
  , maximizes
  , minimizesDef
  , maximizesDef
  , minimizesBy
  , maximizesBy
  , minimizesByDef
  , maximizesByDef
) where

import Data.Functor.Apply (Apply)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Profunctor.Optic
import Data.Semigroup.Foldable as F1
import Prelude
import qualified Data.Foldable as F
import qualified Data.List.NonEmpty as NE
import qualified Data.Profunctor.Rep.Foldl as L
import qualified Data.Profunctor.Rep.Foldl1 as L1

---------------------------------------------------------------------
-- Types
---------------------------------------------------------------------

-- | A < https://en.wikipedia.org/wiki/Moore_machine Moore machine >.
--
type Moore s t a b = forall p. (Closed p, Cotraversing1 p, Foldable (Corep p)) => Optic p s t a b

-- | A < https://en.wikipedia.org/wiki/Mealy_machine Mealy machine >.
--
type Mealy s t a b = forall p. (Coaffine p, Cotraversing p, Foldable1 (Corep p)) => Optic p s t a b

type Moore' t b = Moore t t b b

type Mealy' t b = Mealy t t b b

-- | Reified 'Moore' optic.
type AFoldl s t a b = Optic L.Foldl s t a b

-- | Reified 'Mealy' optic.
type AFoldl1 s t a b = Optic L1.Foldl1 s t a b

---------------------------------------------------------------------
-- Moore
---------------------------------------------------------------------

-- | Obtain a 'Moore' directly.
--
moore :: (s -> a) -> (forall f. Foldable' f => f s -> b -> t) -> Moore s t a b
moore sa sbt p = cotabulate $ \s -> sbt s (cosieve p . fmap sa $ s)
{-# INLINE moore #-}

-- | A < http://events.cs.bham.ac.uk/syco/strings3-syco5/slides/roman.pdf list lens >.
--
listing :: (s -> a) -> ([s] -> b -> t) -> Moore s t a b
listing sa sbt = moore sa $ sbt . F.toList
{-# INLINE listing #-}

-- | Right fold over a 'Moore'.
--
foldingr :: (s -> a) -> (s -> r -> r) -> r -> (r -> b -> t) -> Moore s t a b
foldingr sa h z rbt = moore sa $ rbt . F.foldr h z
{-# INLINE foldingr #-}

-- | Strict right fold over a 'Moore'.
--
foldingr' :: (s -> a) -> (s -> r -> r) -> r -> (r -> b -> t) -> Moore s t a b
foldingr' sa h z rbt = moore sa $ rbt . F.foldr' h z
{-# INLINE foldingr' #-}

-- | Left fold over a 'Moore'.
--
foldingl :: (s -> a) -> (r -> s -> r) -> r -> (r -> b -> t) -> Moore s t a b
foldingl sa h z rbt = moore sa $ rbt . F.foldl h z
{-# INLINE foldingl #-}

-- | Strict left fold over a 'Moore'.
--
foldingl' :: (s -> a) -> (r -> s -> r) -> r -> (r -> b -> t) -> Moore s t a b
foldingl' sa h z rbt = moore sa $ rbt . F.foldl' h z
{-# INLINE foldingl' #-}

-- | Monadic right fold over a 'Moore'.
--
foldingrM :: Monad m => (s -> a) -> (s -> r -> m r) -> r -> (m r -> b -> t) -> Moore s t a b
foldingrM sa h z rbt = moore sa $ rbt . F.foldrM h z
{-# INLINE foldingrM #-}

-- | Monadic left fold over a 'Moore'.
--
foldinglM :: Monad m => (s -> a) -> (r -> s -> m r) -> r -> (m r -> b -> t) -> Moore s t a b
foldinglM sa h z rbt = moore sa $ rbt . F.foldlM h z
{-# INLINE foldinglM #-}

-- | Traverse for effects over a 'Moore'.
--
traversing_ :: Applicative f => (s -> a) -> (s -> f r) -> (f () -> b -> t) -> Moore s t a b
traversing_ sa h sbt = moore sa $ sbt . F.traverse_ h
{-# INLINE traversing_ #-}

-- | Map monadically for effects over a 'Moore'.
--
mappingM_ :: Monad m => (s -> a) -> (s -> m r) -> (m () -> b -> t) -> Moore s t a b
mappingM_ sa h sbt = moore sa $ sbt . F.mapM_ h
{-# INLINE mappingM_ #-}

-- | Fold-map over a 'Moore'.
--
foldMapping :: Monoid r => (s -> a) -> (s -> r) -> (r -> b -> t) -> Moore s t a b
foldMapping sa sr rbt = moore sa $ rbt . F.foldMap sr
{-# INLINE foldMapping #-}

---------------------------------------------------------------------
-- Mealy
---------------------------------------------------------------------

-- | Obtain a 'Mealy' directly.
--
mealy :: (s -> a) -> (forall f. Foldable1' f => f s -> b -> t) -> Mealy s t a b
mealy sa sbt p = cotabulate $ \s -> sbt s (cosieve p . fmap sa $ s)
{-# INLINE mealy #-}

-- | A non-empty list lens.
--
listing1 :: (s -> a) -> (NonEmpty s -> b -> t) -> Mealy s t a b
listing1 sa sbt = mealy sa $ sbt . F1.toNonEmpty
{-# INLINE listing1 #-}

-- | Non-empty right fold over a 'Mealy'.
--
foldingr1 :: (s -> a) -> (s -> s -> s) -> (s -> b -> t) -> Mealy s t a b
foldingr1 sa h sbt = mealy sa $ sbt . F.foldr1 h
{-# INLINE foldingr1 #-}

-- | Non-empty left fold over a 'Mealy'.
--
foldingl1 :: (s -> a) -> (s -> s -> s) -> (s -> b -> t) -> Mealy s t a b
foldingl1 sa h sbt = mealy sa $ sbt . F.foldl1 h
{-# INLINE foldingl1 #-}

-- | Non-empty monadic right fold over a 'Mealy'.
--
foldingrM1 :: Monad m => (s -> a) -> (s -> s -> m s) -> (m s -> b -> t) -> Mealy s t a b
foldingrM1 sa h sbt = mealy sa $ sbt . F1.foldrM1 h
{-# INLINE foldingrM1 #-}

-- | Non-empty monadic left fold over a 'Mealy'.
--
foldinglM1 :: Monad m => (s -> a) -> (s -> s -> m s) -> (m s -> b -> t) -> Mealy s t a b
foldinglM1 sa h sbt = mealy sa $ sbt . F1.foldlM1 h
{-# INLINE foldinglM1 #-}

-- | Traverse for effects over a 'Mealy' (non-empty).
--
traversing1_ :: Apply f => (s -> a) -> (s -> f r) -> (f () -> b -> t) -> Mealy s t a b
traversing1_ sa h sbt = mealy sa $ sbt . F1.traverse1_ h
{-# INLINE traversing1_ #-}

-- | Fold-map over a 'Mealy' (non-empty, semigroup).
--
foldMapping1 :: Semigroup r => (s -> a) -> (s -> r) -> (r -> b -> t) -> Mealy s t a b
foldMapping1 sa sr rbt = mealy sa $ rbt . F1.foldMap1 sr
{-# INLINE foldMapping1 #-}

---------------------------------------------------------------------
-- Optics
---------------------------------------------------------------------

-- | Retain the first out-of-focus part of a lens.
--
head1 :: Lens s t a b -> Mealy s t a b
head1 o = withLens o $ \sa sbt -> listing1 sa $ sbt . NE.head
{-# INLINE head1 #-}

-- | Retain the last out-of-focus part of a lens.
--
last1 :: Lens s t a b -> Mealy s t a b
last1 o = withLens o $ \sa sbt -> listing1 sa $ sbt . NE.last
{-# INLINE last1 #-}

-- | Project away a structure.
--
projected :: (s -> a) -> Moore s b a b
projected sa = moore sa (flip const)
{-# INLINE projected #-}

-- | Minimize over a lens.
--
minimized :: Ord s => Lens s t a b -> Mealy s t a b
minimized o = withLens o $ \sa sbt -> mealy sa $ \fs b -> sbt (F.minimum fs) b
{-# INLINE minimized #-}

-- | Maximize over a lens.
--
maximized :: Ord s => Lens s t a b -> Mealy s t a b
maximized o = withLens o $ \sa sbt -> mealy sa $ \fs b -> sbt (F.maximum fs) b
{-# INLINE maximized #-}

-- | Minimize over a 'Lens' using a default.
--
minimizedDef :: Ord s => s -> Lens s t a b -> Moore s t a b
minimizedDef s o = withLens o $ \sa sbt -> moore sa $ \fs b -> flip sbt b $ maybe s id $ minimumMay fs
{-# INLINE minimizedDef #-}

-- | Maximize over a 'Lens' using a default.
--
maximizedDef :: Ord s => s -> Lens s t a b -> Moore s t a b
maximizedDef s o = withLens o $ \sa sbt -> moore sa $ \fs b -> flip sbt b $ maybe s id $ maximumMay fs
{-# INLINE maximizedDef #-}

-- | Minimize over a 'Lens' using a comparator.
--
minimizedBy :: (s -> s -> Ordering) -> Lens s t a b -> Mealy s t a b
minimizedBy cmp o = withLens o $ \sa sbt -> mealy sa $ \fs b -> sbt (F.minimumBy cmp fs) b
{-# INLINE minimizedBy #-}

-- | Maximize over a 'Lens' using a comparator.
--
maximizedBy :: (s -> s -> Ordering) -> Lens s t a b -> Mealy s t a b
maximizedBy cmp o = withLens o $ \sa sbt -> mealy sa $ \fs b -> sbt (F.maximumBy cmp fs) b
{-# INLINE maximizedBy #-}

-- | Minimize over a 'Lens' using a comparator and a default.
--
minimizedByDef :: (s -> s -> Ordering) -> s -> Lens s t a b -> Moore s t a b
minimizedByDef cmp s o = withLens o $ \sa sbt -> moore sa $ \fs b -> flip sbt b $ maybe s id $ minimumByMay cmp fs
{-# INLINE minimizedByDef #-}

-- | Maximize over a 'Lens' using a comparator and a default.
--
maximizedByDef :: (s -> s -> Ordering) -> s -> Lens s t a b -> Moore s t a b
maximizedByDef cmp s o = withLens o $ \sa sbt -> moore sa $ \fs b -> flip sbt b $ maybe s id $ maximumByMay cmp fs
{-# INLINE maximizedByDef #-}

-- | Search over a 'Lens' using a predicate and a default.
--
foundDef :: (s -> b -> Bool) -> s -> Lens s t a b -> Moore s t a b
foundDef p s o = withLens o $ \sa sbt -> moore sa $ \fs b -> flip sbt b $ maybe s id $ F.find (flip p b) fs
{-# INLINE foundDef #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Fold a structure into a list through an optic.
--
-- @
-- 'listl' o = 'buildl' o 'Data.Profunctor.Rep.Foldl.list'
-- @
--
listl :: Foldable f => AFoldl s t a [a] -> f s -> t
listl o = buildl o L.list
{-# INLINE listl #-}

-- | Fold a non-empty structure into a non-empty list through an optic.
--
listl1 :: Foldable1 f => AFoldl1 s t a (NonEmpty a) -> f s -> t
listl1 o s = flip L1.foldl1 s . o $ L1.list1
{-# INLINE listl1 #-}

-- | Fold a non-empty structure through an optic using a step function.
--
steps :: Foldable1 f => AFoldl1 s t a b -> (x -> a -> x) -> x -> (x -> b) -> f s -> t
steps o h z k = buildl1 o $ L1.Foldl1 h (h z) k
{-# INLINE steps #-}

-- | Fold a structure through an optic using a 'Foldl'.
--
buildl :: Foldable f => AFoldl s t a b -> L.Foldl a b -> f s -> t
buildl o f s = flip L.foldl s . o $ f
{-# INLINE buildl #-}

-- | Fold a structure through an optic using explicit step/begin/done.
--
buildsl :: Foldable f => AFoldl s t a b -> (x -> a -> x) -> x -> (x -> b) -> f s -> t
buildsl o h z k = buildl o $ L.Foldl h z k
{-# INLINE buildsl #-}

-- | Fold a non-empty structure through an optic using a 'Foldl1'.
--
buildl1 :: Foldable1 f => AFoldl1 s t a b -> L1.Foldl1 a b -> f s -> t
buildl1 o f s = flip L1.foldl1 s . o $ f
{-# INLINE buildl1 #-}

-- | Fold a non-empty structure through an optic using explicit step/begin/done.
--
buildsl1 :: Foldable1 f => AFoldl1 s t a b -> (x -> a -> x) -> (a -> x) -> (x -> b) -> f s -> t
buildsl1 o h z k = buildl1 o $ L1.Foldl1 h z k
{-# INLINE buildsl1 #-}

-- | Post-scan a traversable structure through an optic.
--
postscanl :: Traversable f => AFoldl s t a b -> L.Foldl a b -> f s -> f t
postscanl o f s = flip L.postscan s . o $ f
{-# INLINE postscanl #-}

-- | Post-scan a traversable structure through an optic using explicit step/begin/done.
--
postscansl :: Traversable f => AFoldl s t a b -> (x -> a -> x) -> x -> (x -> b) -> f s -> f t
postscansl o h z k = postscanl o $ L.Foldl h z k
{-# INLINE postscansl #-}

-- | Monoidal concatenation through an optic.
--
mconcats :: Foldable f => Monoid m => AFoldl s t a b -> (a -> m) -> (m -> b) -> f s -> t
mconcats o f g s = flip L.foldl s . o $ L.mconcat f g
{-# INLINE mconcats #-}

-- | Semigroup concatenation through an optic.
--
sconcats :: Foldable1 f => Semigroup m => AFoldl1 s t a b -> (a -> m) -> (m -> b) -> f s -> t
sconcats o f g s = flip L1.foldl1 s . o $ L1.sconcat f g
{-# INLINE sconcats #-}

-- | Minimize through a non-empty optic.
--
minimizes :: Foldable1 f => Ord a => AFoldl1 s t a a -> f s -> t
minimizes o = buildl1 o $ L1.minimum
{-# INLINE minimizes #-}

-- | Maximize through a non-empty optic.
--
maximizes :: Foldable1 f => Ord a => AFoldl1 s t a a -> f s -> t
maximizes o = buildl1 o $ L1.maximum
{-# INLINE maximizes #-}

-- | Minimize with a default through an optic.
--
minimizesDef :: Foldable f => Ord a => AFoldl s t a a -> a -> f s -> t
minimizesDef o a = buildl o $ L.minimumDef a
{-# INLINE minimizesDef #-}

-- | Maximize with a default through an optic.
--
maximizesDef :: Foldable f => Ord a => AFoldl s t a a -> a -> f s -> t
maximizesDef o a = buildl o $ L.maximumDef a
{-# INLINE maximizesDef #-}

-- | Minimize using a comparator through a non-empty optic.
--
minimizesBy :: Foldable1 f => AFoldl1 s t a a -> (a -> a -> Ordering) -> f s -> t
minimizesBy o f = buildl1 o $ L1.minimumBy f
{-# INLINE minimizesBy #-}

-- | Maximize using a comparator through a non-empty optic.
--
maximizesBy :: Foldable1 f => AFoldl1 s t a a -> (a -> a -> Ordering) -> f s -> t
maximizesBy o f = buildl1 o $ L1.maximumBy f
{-# INLINE maximizesBy #-}

-- | Minimize using a comparator and a default through an optic.
--
minimizesByDef :: Foldable f => AFoldl s t a a -> (a -> a -> Ordering) -> a -> f s -> t
minimizesByDef o f a = buildl o $ L.minimumByDef f a
{-# INLINE minimizesByDef #-}

-- | Maximize using a comparator and a default through an optic.
--
maximizesByDef :: Foldable f => AFoldl s t a a -> (a -> a -> Ordering) -> a -> f s -> t
maximizesByDef o f a = buildl o $ L.maximumByDef f a
{-# INLINE maximizesByDef #-}

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

liftMay :: (a -> Bool) -> (a -> b) -> a -> Maybe b
liftMay prd f a = if prd a then Nothing else Just $ f a

minimumMay, maximumMay :: Foldable f => Ord a => f a -> Maybe a
minimumMay = liftMay F.null F.minimum
maximumMay = liftMay F.null F.maximum

minimumByMay, maximumByMay :: Foldable f => (a -> a -> Ordering) -> f a -> Maybe a
minimumByMay = liftMay F.null . F.minimumBy
maximumByMay = liftMay F.null . F.maximumBy

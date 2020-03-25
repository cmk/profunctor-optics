{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Machine (
    -- * Types
    Moore
  , Mealy
    -- * Fold
  , moore
  , listing
  , foldingr
  , foldingl
  , foldingrM
  , foldinglM
  , foldMapping
    -- * Mealy 
  , mealy
  , listing1
  , foldingr1
  , foldingl1
  , foldingrM1
  , foldinglM1
  , foldMapping1
  , intercalating
    -- * Optics
  , foldMapped
  , foldMapped1
  , minimized
  , maximized
  , minimizedBy
  , maximizedBy
  , minimizedDef 
  , maximizedDef
  , minimizedByDef
  , maximizedByDef
    -- * Operators
  , buildsl
  , buildsl1
  , listsl
  , listsl1
  , mconcatsl
  , sconcatsl
  , foldMapsl
  , foldMapsl1
) where

import Data.List.NonEmpty as NonEmpty
import Data.Monoid
import Data.Semigroup
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Types
import Data.Semigroup.Foldable as F1
import qualified Data.Foldable as F
import qualified Data.Profunctor.Rep.Foldl as L
import qualified Data.Profunctor.Rep.Foldl1 as L1

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XFlexibleContexts
-- >>> :set -XTypeApplications
-- >>> :set -XTupleSections
-- >>> :set -XRankNTypes
-- >>> import Data.Monoid
-- >>> import Data.Semigroup
-- >>> import Data.List.NonEmpty (NonEmpty(..))
-- >>> import Data.Function ((&))
-- >>> import Data.Foldable
-- >>> import Data.Ord
-- >>> :load Data.Profunctor.Optic

---------------------------------------------------------------------
-- 'Foldl' & 'Foldl1'
---------------------------------------------------------------------

-- | Obtain a 'Foldl' directly.
--
moore :: (s -> a) -> (forall f. Foldable f => f s -> b -> t) -> Moore s t a b
moore sa sbt p = cotabulate $ \s -> sbt s (cosieve p . fmap sa $ s)
{-# INLINE moore #-}

-- | A < http://events.cs.bham.ac.uk/syco/strings3-syco5/slides/roman.pdf list lens >.
--
listing :: (s -> a) -> ([s] -> b -> t) -> Moore s t a b
listing sa sbt = moore sa $ sbt . F.toList
{-# INLINE listing #-}

-- | TODO: Document
--
foldingr :: (s -> a) -> (s -> r -> r) -> r -> (r -> b -> t) -> Moore s t a b
foldingr sa h z rbt = moore sa $ rbt . F.foldr h z
{-# INLINE foldingr #-}

-- | TODO: Document
--
foldingl :: (s -> a) -> (r -> s -> r) -> r -> (r -> b -> t) -> Moore s t a b
foldingl sa h z rbt = moore sa $ rbt . F.foldl h z
{-# INLINE foldingl #-}

-- | TODO: Document
--
foldingrM :: Monad m => (s -> a) -> (s -> r -> m r) -> r -> (m r -> b -> t) -> Moore s t a b
foldingrM sa h z rbt = moore sa $ rbt . F.foldrM h z
{-# INLINE foldingrM #-}

-- | TODO: Document
--
foldinglM :: Monad m => (s -> a) -> (r -> s -> m r) -> r -> (m r -> b -> t) -> Moore s t a b
foldinglM sa h z rbt = moore sa $ rbt . F.foldlM h z
{-# INLINE foldinglM #-}

-- | TODO: Document
--
foldMapping :: Monoid r => (s -> a) -> (s -> r) -> (r -> b -> t) -> Moore s t a b
foldMapping sa sr rbt = moore sa $ rbt . F.foldMap sr
{-# INLINE foldMapping #-}

---------------------------------------------------------------------
-- 'Foldl1'
---------------------------------------------------------------------

-- | Obtain a 'Foldl1' directly.
--
mealy :: (s -> a) -> (forall f. Foldable1 f => f s -> b -> t) -> Mealy s t a b
mealy sa sbt p = cotabulate $ \s -> sbt s (cosieve p . fmap sa $ s)
{-# INLINE mealy #-}

-- | A non-empty list lens.
--
listing1 :: (s -> a) -> (NonEmpty s -> b -> t) -> Mealy s t a b
listing1 sa sbt = mealy sa $ sbt . F1.toNonEmpty
{-# INLINE listing1 #-}

-- | TODO: Document
--
foldingr1 :: (s -> a) -> (s -> s -> s) -> (s -> b -> t) -> Mealy s t a b
foldingr1 sa h sbt = mealy sa $ sbt . F.foldr1 h
{-# INLINE foldingr1 #-}

-- | TODO: Document
--
foldingl1 :: (s -> a) -> (s -> s -> s) -> (s -> b -> t) -> Mealy s t a b
foldingl1 sa h sbt = mealy sa $ sbt . F.foldl1 h
{-# INLINE foldingl1 #-}

-- | TODO: Document
--
foldingrM1 :: Monad m => (s -> a) -> (s -> s -> m s) -> (m s -> b -> t) -> Mealy s t a b
foldingrM1 sa h sbt = mealy sa $ sbt . F1.foldrM1 h
{-# INLINE foldingrM1 #-}

-- | TODO: Document
--
foldinglM1 :: Monad m => (s -> a) -> (s -> s -> m s) -> (m s -> b -> t) -> Mealy s t a b
foldinglM1 sa h sbt = mealy sa $ sbt . F1.foldlM1 h
{-# INLINE foldinglM1 #-}

-- | TODO: Document
--
foldMapping1 :: Semigroup r => (s -> a) -> (s -> r) -> (r -> b -> t) -> Mealy s t a b
foldMapping1 sa sr rbt = mealy sa $ rbt . F1.foldMap1 sr
{-# INLINE foldMapping1 #-}

-- | TODO: Document
--
intercalating :: Semigroup r => (s -> a) -> (s -> r) -> r -> (r -> b -> t) -> Mealy s t a b
intercalating sa sr r rbt = mealy sa $ rbt . F1.intercalateMap1 r sr
{-# INLINE intercalating #-}

---------------------------------------------------------------------
-- Optics
---------------------------------------------------------------------

-- | TODO: Document
--
-- >>> buildsl (foldMapped second') (++) [] id [(Sum 1,"one"),(Sum 2,"two")]
-- (Sum {getSum = 3},"onetwo")
--
foldMapped :: Monoid s => Lens s t a b -> Moore s t a b
foldMapped o = withLens o $ \sa sbt -> foldMapping sa id sbt
{-# INLINE foldMapped #-}

-- | TODO: Document
--
foldMapped1 :: Semigroup s => Lens s t a b -> Mealy s t a b
foldMapped1 o = withLens o $ \sa sbt -> foldMapping1 sa id sbt
{-# INLINE foldMapped1 #-}

-- | TODO: Document
--
minimized :: Ord s => Lens s t a b -> Mealy s t a b
minimized o = withLens o $ \sa sbt -> mealy sa $ \fs b -> sbt (F.minimum fs) b
{-# INLINE minimized #-}

-- | TODO: Document
--
-- >>> listsl1 (maximized second') $ (0,"zero") :| [(1,"one"),(2,"two")]
-- (2,"zero" :| ["one","two"])
-- >>> buildsl1 (maximized second') (++) id id $ (0,"zero") :| [(1,"one"),(2,"two")] 
-- (2,"zeroonetwo")
--
maximized :: Ord s => Lens s t a b -> Mealy s t a b
maximized o = withLens o $ \sa sbt -> mealy sa $ \fs b -> sbt (F.maximum fs) b
{-# INLINE maximized #-}

-- | TODO: Document
--
minimizedBy :: (s -> s -> Ordering) -> Lens s t a b -> Mealy s t a b
minimizedBy cmp o = withLens o $ \sa sbt -> mealy sa $ \fs b -> sbt (F.minimumBy cmp fs) b 
{-# INLINE minimizedBy #-}

-- | TODO: Document
--
maximizedBy :: (s -> s -> Ordering) -> Lens s t a b -> Mealy s t a b
maximizedBy cmp o = withLens o $ \sa sbt -> mealy sa $ \fs b -> sbt (F.maximumBy cmp fs) b 
{-# INLINE maximizedBy #-}

-- | TODO: Document
--
-- >>> listsl (minimizedDef (0,[]) second') [(1,"one"),(2,"two")]
-- (1,["one","two"])
-- >>> listsl (minimizedDef (0,[]) second' . cotraversed1) [(1,"one"),(2,"two")]
-- (1,["ot","nw","eo"])
--
minimizedDef :: Ord s => t -> Lens s t a b -> Moore s t a b
minimizedDef t o = withLens o $ \sa sbt -> moore sa $ \fs b -> maybe t (flip sbt b) $ minimumMay fs
{-# INLINE minimizedDef #-}

-- | TODO: Document
--
maximizedDef :: Ord s => t -> Lens s t a b -> Moore s t a b
maximizedDef t o = withLens o $ \sa sbt -> moore sa $ \fs b -> maybe t (flip sbt b) $ maximumMay fs
{-# INLINE maximizedDef #-}

-- | TODO: Document
--
minimizedByDef :: (s -> s -> Ordering) -> t -> Lens s t a b -> Moore s t a b
minimizedByDef cmp t o = withLens o $ \sa sbt -> moore sa $ \fs b -> maybe t (flip sbt b) $ minimumByMay cmp fs 
{-# INLINE minimizedByDef #-}

-- | TODO: Document
--
maximizedByDef :: (s -> s -> Ordering) -> t -> Lens s t a b -> Moore s t a b
maximizedByDef cmp t o = withLens o $ \sa sbt -> moore sa $ \fs b -> maybe t (flip sbt b) $ maximumByMay cmp fs 
{-# INLINE maximizedByDef #-}

{-
-- | TODO: Document
--
prefiltered :: (a -> Bool) -> AFoldl a b a b
prefiltered = L.prefilter
{-# INLINE prefiltered #-}


-- requires latest version of foldl
dropped :: Natural -> AFoldl' a b
dropped = L.drop

-- requires latest version of foldl
predroppedWhile :: (a -> Bool) -> AFoldl' a b
predroppedWhile = L.predropWhile
-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | TODO: Document
--
-- A left-hand, optic version of the < http://hackage.haskell.org/package/base-4.12.0.0/docs/src/GHC.Base.html#build /build/ > in 'GHC.Base'.
--
-- >>> buildsl (foldMapped second') (++) [] id [(Sum 1,"one"),(Sum 2,"two")]
-- (Sum {getSum = 3},"onetwo")
-- 
buildsl :: Foldable f => AFoldl s t a b -> (x -> a -> x) -> x -> (x -> b) -> f s -> t
buildsl o h z k s = flip L.fold s . o $ L.Fold h z k
{-# INLINE buildsl #-}

-- | TODO: Document
--
-- >>> buildsl1 (foldMapped1 second') (++) id id $ (Min 0, "zero") :| [(Min 1,"one"),(Min 2,"two")]
-- (Min {getMin = 0},"zeroonetwo")
-- 
buildsl1 :: Foldable1 f => AFoldl1 s t a b -> (x -> a -> x) -> (a -> x) -> (x -> b) -> f s -> t
buildsl1 o h z k s = flip L1.foldl1 s . o $ L1.Foldl1 h z k
{-# INLINE buildsl1 #-}

-- | TODO: Document
--
-- > 'listsl' id = 'Control.Foldl.fold' 'Control.Foldl.list' = 'Data.Foldable.toList'
--
-- >>> listsl closed [("foo: "++) . show, ("bar: "++) . show] 42
-- ["foo: 42","bar: 42"]
--
listsl :: Foldable f => AFoldl s t a [a] -> f s -> t
listsl o s = flip L.fold s . o $ L.list
{-# INLINE listsl #-}

-- | TODO: Document
--
listsl1 :: Foldable1 f => AFoldl1 s t a (NonEmpty a) -> f s -> t
listsl1 o s = flip L1.foldl1 s . o $ L1.list1
{-# INLINE listsl1 #-}

-- | TODO: Document
--
mconcatsl :: Foldable f => Monoid m => AFoldl s t m m -> f s -> t
mconcatsl o s = flip L.fold s . o $ L.mconcat
{-# INLINE mconcatsl #-}

-- | TODO: Document
--
sconcatsl :: Foldable1 f => Semigroup m => AFoldl1 s t m m -> f s -> t
sconcatsl o s = flip L1.foldl1 s . o $ L1.sconcat
{-# INLINE sconcatsl #-}

-- | TODO: Document
--
foldMapsl :: Foldable f => Monoid m => AFoldl s t a b -> (a -> m) -> (m -> b) -> f s -> t
foldMapsl o f g s = flip L.fold s . o $ L.foldMap f g
{-# INLINE foldMapsl #-}

-- | TODO: Document
--
foldMapsl1 :: Foldable1 f => Semigroup m => AFoldl1 s t a b -> (a -> m) -> (m -> b) -> f s -> t
foldMapsl1 o f g s = flip L1.foldl1 s . o $ L1.foldMap1 f g
{-# INLINE foldMapsl1 #-}

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

module Data.Profunctor.Optic.Sequence (
    -- * Isos
    strict
  , chunked
  , unpacked
  , reversed
    -- * Packing
  , packing
  , packing1
  , chunking
    -- * Sequential optics
  , packed
  , packed'
  , taken
  , taken'
  , padded
  , padded'
  , takenWhile
  , takenWhile'
  , droppedWhile
  , droppedWhile'
  , filteredBy
  , filteredBy'
  , filteredBy1
  , broken
  , spanned
  , partitioned
  , partitioned'
  , groupedAllOn
  , splitWhen
  , splitFirst
    -- * Operators
  , obuildl
  , obuildsl
  , obuildl1
  , obuildsl1
    -- * Re-exports
  , module Data.Profunctor.Optic.Machine
) where

import Data.MonoTraversable (MonoFoldable(..), Element)
import Data.NonNull (NonNull)
import Data.Profunctor.Optic
import Data.Profunctor.Optic.Machine
import Data.Semigroup.Foldable as F1
import Prelude
import qualified Data.Foldable as F
import qualified Data.MonoTraversable as MT
import qualified Data.NonNull as NN
import qualified Data.Profunctor.Rep.Foldl as L
import qualified Data.Profunctor.Rep.Foldl1 as L1
import qualified Data.Sequences as MS

---------------------------------------------------------------------
-- Isos
---------------------------------------------------------------------

-- | Iso between a lazy sequence and its strict counterpart.
--
strict :: MS.LazySequence l s => Iso' l s
strict = iso MS.toStrict MS.fromStrict
{-# INLINE strict #-}

-- | Iso between a lazy sequence and a list of strict chunks.
--
chunked :: MS.LazySequence l s => Iso' l [s]
chunked = iso MS.toChunks MS.fromChunks
{-# INLINE chunked #-}

-- | Iso between a sequence and a list of its elements.
--
unpacked :: MS.IsSequence s => Iso' s [Element s]
unpacked = iso MS.unpack MS.pack
{-# INLINE unpacked #-}

-- | Iso that reverses a sequence.
--
reversed :: MS.IsSequence s => Iso' s s
reversed = iso MS.reverse MS.reverse
{-# INLINE reversed #-}

---------------------------------------------------------------------
-- Packing
---------------------------------------------------------------------

-- | Pack elements into an 'IsSequence' through a 'Moore'.
--
packing :: MS.IsSequence s => (Element s -> a) -> (s -> b -> t) -> Moore (Element s) t a b
packing sa sbt = moore sa $ sbt . MS.pack . F.toList
{-# INLINEABLE packing #-}

-- | Pack elements into a 'NonNull' sequence through a 'Mealy'.
--
packing1 :: MS.IsSequence s => (Element s -> a) -> (NonNull s -> b -> t) -> Mealy (Element s) t a b
packing1 sa sbt = mealy sa $ sbt . NN.fromNonEmpty . F1.toNonEmpty
{-# INLINE packing1 #-}

-- | Chunk strict sequenceOf into a lazy sequence through a 'Moore'.
--
chunking :: MS.LazySequence l s => (s -> a) -> (l -> b -> t) -> Moore s t a b
chunking sa sbt = moore sa $ sbt . MS.fromChunks . F.toList
{-# INLINEABLE chunking #-}

---------------------------------------------------------------------
-- Sequential optics
---------------------------------------------------------------------

-- | Pack elements of a lens into a sequence.
--
packed :: MS.IsSequence s => Lens s t a b -> Moore (Element s) t a b
packed o = withLens o $ \sa sbt -> packing (sa . MT.opoint) sbt

-- | Pack chunks of a lens into a lazy sequence.
--
packed' :: MS.LazySequence l s => Lens l t a b -> Moore s t a b
packed' o = withLens o $ \la lbt -> chunking (la . MS.fromStrict) lbt
{-# INLINE packed' #-}

-- | Take a number of elements from a sequence.
--
taken :: MS.IsSequence s => (b -> MS.Index s) -> Moore (Element s) s (Element s) b
taken f = packing id $ \s b -> MS.take (f b) s

-- | Take a number of chunks from a lazy sequence.
--
taken' :: MS.LazySequence l s => (b -> MS.Index l) -> Moore s l (MS.Index s) b
taken' f = chunking MS.lengthIndex $ \s b -> MS.take (f b) s
{-# INLINE taken' #-}

-- | Pad sequenceOf to a uniform length.
--
padded :: MS.IsSequence s => Element s -> Moore s [s] (MS.Index s) (MS.Index s)
padded w = listing MS.lengthIndex $ \s b -> fmap (\x -> MS.take b (x <> MS.replicate b w)) s
{-# INLINE padded #-}

-- | Pad chunks to a uniform length in a lazy sequence.
--
padded' :: MS.LazySequence l s => Element s -> Moore s l (MS.Index s) (MS.Index s)
padded' w = moore MS.lengthIndex $ \bs n -> MS.fromChunks $
  fmap (\s -> MS.take n $ s <> MS.replicate n w) $ F.toList bs
{-# INLINE padded' #-}

-- | Take elements while a predicate holds.
--
takenWhile :: MS.IsSequence s => (Element s -> a) -> (Element s -> b -> Bool) -> Moore (Element s) s a b
takenWhile sa sbt = packing sa $ \s b -> MS.takeWhile (flip sbt b) s
{-# INLINE takenWhile #-}

-- | Take chunks while a predicate holds on a lazy sequence.
--
takenWhile' :: MS.LazySequence l s => (s -> a) -> (Element l -> b -> Bool) -> Moore s l a b
takenWhile' sa sbt = chunking sa $ \s b -> MS.takeWhile (flip sbt b) s
{-# INLINE takenWhile' #-}

-- | Drop elements while a predicate holds.
--
droppedWhile :: MS.IsSequence s => (Element s -> a) -> (Element s -> b -> Bool) -> Moore (Element s) s a b
droppedWhile sa sbt = packing sa $ \s b -> MS.dropWhile (flip sbt b) s
{-# INLINE droppedWhile #-}

-- | Drop chunks while a predicate holds on a lazy sequence.
--
droppedWhile' :: MS.LazySequence l s => (s -> a) -> (Element l -> b -> Bool) -> Moore s l a b
droppedWhile' sa sbt = chunking sa $ \s b -> MS.dropWhile (flip sbt b) s
{-# INLINE droppedWhile' #-}

-- | Filter elements of a sequence.
--
filteredBy :: MS.IsSequence s => (Element s -> a) -> (Element s -> b -> Bool) -> Moore (Element s) s a b
filteredBy sa sbt = packing sa $ \s b -> MS.filter (flip sbt b) s
{-# INLINE filteredBy #-}

-- | Filter chunks of a lazy sequence.
--
filteredBy' :: MS.LazySequence l s => (s -> a) -> (Element l -> b -> Bool) -> Moore s l a b
filteredBy' sa sbt = chunking sa $ \s b -> MS.filter (flip sbt b) s
{-# INLINE filteredBy' #-}

-- | Filter elements of a non-empty sequence.
--
filteredBy1 :: MS.IsSequence s => (Element s -> a) -> (Element s -> b -> Bool) -> Mealy (Element s) s a b
filteredBy1 sa sbt = packing1 sa $ \s b -> NN.nfilter (flip sbt b) s
{-# INLINE filteredBy1 #-}

-- | Break a sequence at the first element matching a predicate.
--
broken :: MS.IsSequence s => (Element s -> a) -> (Element s -> b -> Bool) -> Moore (Element s) (s, s) a b
broken sa sbt = packing sa $ \s b -> MS.break (flip sbt b) s
{-# INLINE broken #-}

-- | Span a sequence while a predicate holds.
--
spanned :: MS.IsSequence s => (Element s -> a) -> (Element s -> b -> Bool) -> Moore (Element s) (s, s) a b
spanned sa sbt = packing sa $ \s b -> MS.span (flip sbt b) s
{-# INLINE spanned #-}

-- | Partition a sequence by a predicate.
--
partitioned :: MS.IsSequence s => (Element s -> a) -> (Element s -> b -> Bool) -> Moore (Element s) (s, s) a b
partitioned sa sbt = packing sa $ \s b -> MS.partition (flip sbt b) s
{-# INLINE partitioned #-}

-- | Partition chunks of a lazy sequence.
--
partitioned' :: MS.LazySequence l s => (s -> a) -> (Element l -> b -> Bool) -> Moore s (l, l) a b
partitioned' sa sbt = chunking sa $ \s b -> MS.partition (flip sbt b) s
{-# INLINE partitioned' #-}

-- | Group elements by equality on a projection.
--
groupedAllOn :: MS.IsSequence s => Eq r => (Element s -> a) -> (Element s -> b -> r) -> Moore (Element s) [s] a b
groupedAllOn sa sbt = packing sa $ \s b -> MS.groupAllOn (flip sbt b) s
{-# INLINE groupedAllOn #-}

-- | Split a sequence at elements matching a predicate.
--
splitWhen :: MS.IsSequence s => (Element s -> a) -> (Element s -> b -> Bool) -> Moore (Element s) [s] a b
splitWhen sa sbt = packing sa $ \s b -> MS.splitWhen (flip sbt b) s
{-# INLINE splitWhen #-}

-- | Split a non-empty sequence at the first element.
--
splitFirst :: MS.IsSequence s => (Element s -> a) -> ((Element s, s) -> b -> t) -> Mealy (Element s) t a b
splitFirst sa sbt = packing1 sa $ sbt . NN.splitFirst
{-# INLINE splitFirst #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Fold a 'MonoFoldable' through an optic using a 'Foldl'.
--
obuildl :: MonoFoldable s => AFoldl (Element s) t a b -> L.Foldl a b -> s -> t
obuildl o f = (`L.withFoldl` MT.ofoldlUnwrap) . o $ f
{-# INLINE obuildl #-}

-- | Fold a 'MonoFoldable' through an optic using explicit step/begin/done.
--
obuildsl :: MonoFoldable s => AFoldl (Element s) t a b -> (x -> a -> x) -> x -> (x -> b) -> s -> t
obuildsl o h z k = obuildl o $ L.Foldl h z k
{-# INLINE obuildsl #-}

-- | Fold a non-empty 'IsSequence' through an optic using a 'Foldl1'.
--
obuildl1 :: MS.IsSequence s => AFoldl1 (Element s) t a b -> L1.Foldl1 a b -> NonNull s -> t
obuildl1 o f = (`L1.withFoldl1` ofoldl1Unwrap) . o $ f
{-# INLINE obuildl1 #-}

-- | Fold a non-empty 'IsSequence' through an optic using explicit step/begin/done.
--
obuildsl1 :: MS.IsSequence s => AFoldl1 (Element s) t a b -> (x -> a -> x) -> (a -> x) -> (x -> b) -> NonNull s -> t
obuildsl1 o h z k = obuildl1 o $ L1.Foldl1 h z k
{-# INLINE obuildsl1 #-}

---------------------------------------------------------------------
-- Internal
---------------------------------------------------------------------

ofoldl1Unwrap :: MS.IsSequence s => (x -> Element s -> x) -> (Element s -> x) -> (x -> b) -> NonNull s -> b
ofoldl1Unwrap h z k nnull = k (ofoldl' h (z initial) s) where (initial,s) = NN.splitFirst nnull

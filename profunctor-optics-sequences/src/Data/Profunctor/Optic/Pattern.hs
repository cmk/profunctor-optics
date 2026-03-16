module Data.Profunctor.Optic.Pattern (
    pattern Lazy
  , pattern Strict
  , pattern Chunked
  , pattern Packed
  , pattern Unpacked
  , pattern Swapped
  , pattern Reversed
) where

import Data.MonoTraversable (Element)
import Data.Profunctor.Optic (Iso', view, review, re, swapped)
import Data.Profunctor.Optic.Sequence (strict, chunked, unpacked, reversed)
import Data.Sequences (LazySequence, IsSequence)
import Prelude

pattern Lazy :: LazySequence l s => l -> s
pattern Lazy a <- (view (re strict) -> a) where Lazy a = review (re strict) a

pattern Strict :: LazySequence l s => s -> l
pattern Strict a <- (view strict -> a) where Strict a = review strict a

pattern Chunked :: LazySequence l s => [s] -> l
pattern Chunked a <- (view chunked -> a) where Chunked a = review chunked a

pattern Packed :: IsSequence s => s -> [Element s]
pattern Packed a <- (view (re unpacked) -> a) where Packed a = review (re unpacked) a

pattern Unpacked :: IsSequence s => [Element s] -> s
pattern Unpacked a <- (view unpacked -> a) where Unpacked a = review unpacked a

pattern Swapped :: (a, b) -> (b, a)
pattern Swapped a <- (view swapped -> a) where Swapped a = review swapped a

pattern Reversed :: IsSequence s => s -> s
pattern Reversed a <- (view reversed -> a) where Reversed a = review reversed a

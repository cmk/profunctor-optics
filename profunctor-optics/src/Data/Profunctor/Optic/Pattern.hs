{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE ViewPatterns          #-}
{-# LANGUAGE PatternSynonyms       #-}
module Data.Profunctor.Optic.Pattern where

import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Iso
import Data.Profunctor.Optic.View
import Data.MonoTraversable (Element)
import Data.Sequences

pattern Lazy :: LazySequence l s => l -> s
pattern Lazy a <- (view (re strict) -> a) where
  Lazy a = review (re strict) a

pattern Strict :: LazySequence l s => s -> l
pattern Strict a <- (view strict -> a) where
  Strict a = review strict a

pattern Chunked :: LazySequence l s => [s] -> l
pattern Chunked a <- (view chunked -> a) where
  Chunked a = review chunked a

pattern Packed :: IsSequence s => s -> [Element s]
pattern Packed a <- (view (re unpacked) -> a) where
  Packed a = review (re unpacked) a

pattern Unpacked :: IsSequence s => [Element s] -> s
pattern Unpacked a <- (view unpacked -> a) where
  Unpacked a = review unpacked a

pattern Swapped :: (a, b) -> (b, a)
pattern Swapped a <- (view swapped -> a) where
  Swapped a = review swapped a

pattern Reversed :: IsSequence s => s -> s
pattern Reversed a <- (view reversed -> a) where
  Reversed a = review reversed a

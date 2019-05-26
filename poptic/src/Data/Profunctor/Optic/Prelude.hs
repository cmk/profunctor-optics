module Data.Profunctor.Optic.Prelude (
    module Data.Profunctor.Optic.Prelude
  , module Export
) where

import Data.Bifunctor                  as Export
import Data.Functor.Apply              as Export
import Data.Functor.Const              as Export
import Data.Functor.Contravariant      as Export
import Data.Functor.Identity           as Export
import Data.Semigroup.Traversable      as Export
import Data.Profunctor.Types           as Export
import Control.Arrow                   as Export ((|||),(***),(&&&)) 
import Control.Composition             as Export hiding (both)

import Data.Void (absurd)

retagged :: (Bifunctor p, Profunctor p) => p a c -> p b c
retagged = first absurd . lmap absurd
{-# INLINE retagged #-}

-- | The 'mempty' equivalent for a 'Contravariant' 'Applicative' 'Functor'.
noEffect :: (Contravariant f, Applicative f) => f a
noEffect = phantom $ pure ()
{-# INLINE noEffect #-}

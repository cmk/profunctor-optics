{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE TypeFamilies          #-}
-- | Structural optics for 'Data.Map.Map' via pattern functors.
--
-- These require @scheme-extensions@ for 'Data.Functor.Fixed.Mu'
-- and 'Data.Functor.Foldable.fold'.
module Data.Map.Fold.Optic (
    -- * Structural (via pattern functor)
    depth
  , sizes
  , rebalanced
) where

import Data.Container.Pattern
import Data.Functor.Foldable (fold)
import qualified Data.Map.Lazy as Map

-- | Compute the depth of a 'Map.Map' using its tree structure.
--
depth :: Map.Map k v -> Int
depth = fold alg . toMapF
  where
    alg MapTip = 0
    alg (MapBin _ _ _ l r) = 1 + max l r

-- | Collect the sizes stored at each internal node.
--
sizes :: Map.Map k v -> [Int]
sizes = fold alg . toMapF
  where
    alg MapTip = []
    alg (MapBin sz _ _ l r) = sz : l ++ r

-- | Rebuild a 'Map.Map' from its pattern functor representation.
--
-- @rebalanced = fromMapF . toMapF@
--
rebalanced :: Map.Map k v -> Map.Map k v
rebalanced = fromMapF . toMapF

{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE TypeFamilies          #-}
-- | Left and right carriers are characterized by their representation
-- functors ('Rep' and 'Corep'). 'Iso' sits at the top where both
-- are trivial ('Identity'). 'Adjoint' sits at the bottom where they
-- form a full adjunction (@'Corep' p ⊣ 'Rep' p@). A left-indexed
-- ('Ix') optic threads an index through the left adjoint functor
-- @(,) k@, while a right-indexed ('Cx') optic threads a coindex
-- through the right adjoint functor @(->) k@.
--
-- Structural optics for 'Data.Map.Map' via pattern functors.
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

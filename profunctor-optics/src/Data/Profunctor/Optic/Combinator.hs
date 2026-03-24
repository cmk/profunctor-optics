-- | Backwards-compatibility shim. All exports have moved:
--
-- * Index\/coindex operations -> "Data.Profunctor.Optic.Index"
-- * Arrow\/Divisible combinators -> "Data.Profunctor.Optic.Traversal"
-- * Utilities (over, star, costar, coercion optics) -> "Data.Profunctor.Optic.Import"
module Data.Profunctor.Optic.Combinator (
    module Data.Profunctor.Optic.Index
  , module Data.Profunctor.Optic.Import
) where

import Data.Profunctor.Optic.Index
import Data.Profunctor.Optic.Import

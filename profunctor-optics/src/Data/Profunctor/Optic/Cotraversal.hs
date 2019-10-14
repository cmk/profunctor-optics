module Data.Profunctor.Optic.Cotraversal where

import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Prelude

---------------------------------------------------------------------
-- 'Cotraversal'
---------------------------------------------------------------------

cotraversed :: Distributive f => Cotraversal (f a) (f b) a b 
cotraversed = lower cotraverse

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- @ cotraverseOf $ grate (flip cotraverse id) == cotraverse @
cotraverseOf :: GrateLike f s t a b -> (f a -> b) -> (f s -> t)
cotraverseOf = between runCostar Costar

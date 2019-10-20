module Data.Profunctor.Optic.Cotraversal where

import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Prelude

---------------------------------------------------------------------
-- 'Cotraversal'
---------------------------------------------------------------------

cotraversed :: Distributive f => Cotraversal (f a) (f b) a b 
cotraversed = undefined --lower cotraverse

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- @ cotraverseOf $ grate (flip cotraverse id) == cotraverse @
cotraverseOf :: Optic (Costar f) s t a b -> (f a -> b) -> (f s -> t)
cotraverseOf = between runCostar Costar

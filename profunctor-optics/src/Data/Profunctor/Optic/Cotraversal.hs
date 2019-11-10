module Data.Profunctor.Optic.Cotraversal where

import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Prelude

---------------------------------------------------------------------
-- 'Cotraversal'
---------------------------------------------------------------------

-- | Transform a Van Laarhoven 'Cotraversal' into a profunctor 'Cotraversal'.
--
cotraversing :: (forall f. Functor f => (f a -> b) -> f s -> t) -> Cotraversal s t a b
cotraversing = lower

-- | TODO: Document
--
cotraversed :: Distributive f => Cotraversal (f a) (f b) a b 
cotraversed = cotraversing cotraverse

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- ^ @
-- 'cotraverseOf' $ 'Data.Profuncto.Optic.Grate.grate' (flip 'Data.Distributive.cotraverse' id) ≡ 'Data.Distributive.cotraverse'
-- @
--
cotraverseOf :: Optic (Costar f) s t a b -> (f a -> b) -> (f s -> t)
cotraverseOf = between runCostar Costar

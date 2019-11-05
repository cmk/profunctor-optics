module Data.Profunctor.Optic.Cotraversal where

import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Prelude

---------------------------------------------------------------------
-- 'Cotraversal'
---------------------------------------------------------------------

-- | TODO: Document
--
cotraversed :: Distributive f => Cotraversal (f a) (f b) a b 
cotraversed = lower cotraverse

-- | Transform a Van Laarhoven 'Cotraversal' into a profunctor 'Cotraversal'.
--
cotraversalVL :: (forall f. Functor f => (f a -> b) -> f s -> t) -> Cotraversal s t a b
cotraversalVL = lower

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- ^ @
-- 'cotraverseOf' $ 'Data.Profuncto.Optic.Grate.grate' (flip 'Data.Distributive.cotraverse' id) ≡ 'Data.Distributive.cotraverse'
-- @
--
cotraverseOf :: Optic (Costar f) s t a b -> (f a -> b) -> (f s -> t)
cotraverseOf = between runCostar Costar

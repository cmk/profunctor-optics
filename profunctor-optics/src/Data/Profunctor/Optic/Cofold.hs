module Data.Profunctor.Optic.Cofold where

import Data.Functor.Foldable (Corecursive, Base)
import Data.Profunctor.Optic.Cotraversal
import Data.Profunctor.Optic.Prelude
import Data.Profunctor.Optic.View
import Data.Profunctor.Optic.Type
import qualified Data.List as L (unfoldr)
import qualified Data.Functor.Foldable as F

---------------------------------------------------------------------
-- 'Cofold'
---------------------------------------------------------------------

-- | Transform a Van Laarhoven 'Cofold' into a profunctor 'Cofold'.
--
cofolding :: (forall f. Functor f => (f a -> b) -> f s -> t) -> Cofold t b
cofolding f = coercel . lower f . coercel
{-# INLINE cofolding #-}

-- | TODO: Document
--
cofolded :: Distributive f => (b -> t) -> Cofold (f t) b
cofolded f = cotraversed . from f
{-# INLINE cofolded #-}

-- | Build a 'Cofold' from a 'Review'.
--
toCofold :: AReview t b -> Cofold t b
toCofold = from . review
{-# INLINE toCofold #-}

-- | Build a 'Review' from a 'Cofold'.
--
fromCofold :: ACofold b t b -> Review t b
fromCofold = cloneReview 
{-# INLINE fromCofold #-}

---------------------------------------------------------------------
-- 'CofoldRep'
---------------------------------------------------------------------

-- | TODO: Document
--
acofold :: ((r -> b) -> r -> t) -> ACofold r t b
acofold = between (Costar . (. getConst)) ((. Const) . runCostar)
{-# INLINE acofold #-}

-- | TODO: Document
--
acofold' :: ACofold b [t] (Maybe (t, b))
acofold' = acofold L.unfoldr
{-# INLINE acofold' #-}

-- | TODO: Document
--
corecursing :: Corecursive t => ACofold b t (Base t b)
corecursing = acofold F.unfold
{-# INLINE corecursing #-}

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | TODO: Document
--
cofoldMapOf :: ACofold r t b -> (r -> b) -> r -> t
cofoldMapOf = between ((. Const) . runCostar) (Costar . (. getConst))
{-# INLINE cofoldMapOf #-}

-- | TODO: Document
--
cofoldOf :: AReview t b -> b -> t
cofoldOf = flip cofoldMapOf id
{-# INLINE cofoldOf #-}

{-# LANGUAGE TupleSections #-}


module Data.Profunctor.Optic.Traversal1 (
    module Data.Profunctor.Optic.Traversal1 
  , module Export
) where

import Data.Bitraversable 
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Operator
import Data.Profunctor.Optic.Prelude

import Data.Profunctor.Optic.Type.Class as Export (Traversing1(..))

import Data.Semigroup.Traversable.Class as Export


---------------------------------------------------------------------
-- 'Traversal1'
---------------------------------------------------------------------

traversed1 :: Traversable1 t => Traversal1 (t a) (t b) a b
traversed1 = wander1 traverse1

-- | Traverse both parts of a 'Bitraversable1' container with matching types.
--
-- Usually that type will be a pair.
--
-- @
-- 'both1' :: 'Traversal1' (a, a)       (b, b)       a b
-- 'both1' :: 'Traversal1' ('Either' a a) ('Either' b b) a b
-- @
both1 :: Bitraversable1 r => Traversal1 (r a a) (r b b) a b
both1 = wander1 $ \f -> bitraverse1 f f
{-# INLINE both1 #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

{-
sequence1Of
  :: Apply f
  => Optic (Star f) s t (f a) a -> s -> f t
sequence1Of t = traverse1Of t id
-}

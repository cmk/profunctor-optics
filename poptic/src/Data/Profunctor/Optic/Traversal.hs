module Data.Profunctor.Optic.Traversal (
    module Data.Profunctor.Optic.Traversal 
  , module Export
) where

import Data.Bitraversable 
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Operator
import Data.Profunctor.Optic.Operator.Task
import Data.Profunctor.Optic.Prelude

import Data.Profunctor.Optic.Traversal.Affine    as Export
import Data.Profunctor.Optic.Traversal.NonEmpty  as Export
import Data.Profunctor.Traversing                as Export

import qualified Data.Profunctor.Optic.Type.VL as VL





---------------------------------------------------------------------
-- 'Traversal'
---------------------------------------------------------------------

traversed :: Traversable t => Traversal (t a) (t b) a b
traversed = wander traverse

-- | Traverse both parts of a 'Bitraversable' container with matching types.
--
-- Usually that type will be a pair.
--
-- >>> (1,2) & both *~ 10
-- (10,20)
--
-- >>> over both length ("hello","world")
-- (5,5)
--
-- >>> ("hello","world")^.both
-- "helloworld"
--
-- @
-- 'both' :: 'Traversal' (a, a)       (b, b)       a b
-- 'both' :: 'Traversal' ('Either' a a) ('Either' b b) a b
-- @
both :: Bitraversable t => Traversal (t a a) (t b b) a b
both = wander $ \f -> bitraverse f f
{-# INLINE both #-}


---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

sequenceOf :: Applicative f => Traversal s t (f a) a -> s -> f t
sequenceOf t = traverseOf t id



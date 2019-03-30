module Data.Profunctor.Optic.Traversal (
    module Data.Profunctor.Optic.Traversal 
  , module Export
) where

import Data.Bitraversable 
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Operators

import Data.Profunctor.Traversing as Export

---------------------------------------------------------------------
-- Traversal
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
-- Derived operators
---------------------------------------------------------------------

sequenceOf
  :: Applicative f
  => Optic (Star f) s t (f a) a -> s -> f t
sequenceOf t = traverseOf t id

-- | More permissive version of 'match' that can satisfy optics with
--
-- a 'Traversing' constraint.
match' :: Optic (Star (Either a)) s t a b -> s -> Either t a
match' o =
 let Star h = o (Star Left)

  in switch . h


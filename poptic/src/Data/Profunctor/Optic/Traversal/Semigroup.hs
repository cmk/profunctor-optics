{-# LANGUAGE TupleSections #-}

module Data.Profunctor.Optic.Traversal.Semigroup (
    module Export
  , module Data.Profunctor.Optic.Traversal.Semigroup
) where

import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Operator
import Data.Profunctor.Optic.Prelude

import Data.Profunctor.Optic.Type.Class as Export (Traversing1(..))
import Data.Semigroup.Traversable.Class as Export


---------------------------------------------------------------------
-- 'Traversal1'
---------------------------------------------------------------------

{-
The laws of Traversal can be stated for Traversal1 too.

Identity:

traverse1Of t (Id . f) ≡  Id (fmap f)

Composition:

Compose . fmap (traverse1Of t f) . traverse1Of t g ≡ traverse1Of t (Compose . fmap f . g)
-}

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

-- | Form a 'Traversal1'' by repeating the input forever.
--
-- @
-- 'repeat' ≡ 'toListOf' 'repeated'
-- @
--
-- >>> take 5 $ 5 ^.. repeated
-- [5,5,5,5,5]
--
-- @
-- repeated :: Fold1 a a
-- @
repeated :: Traversal1' a a
repeated = wander1 $ \g a -> go g a where go g a = g a .> go g a
{-# INLINE repeated #-}


-- | Transform a 'Traversal1'' into a 'Traversal1'' that loops over its elements repeatedly.
--
-- >>> take 7 $ (1 :| [2,3]) ^.. (cycled traversed1)
-- [1,2,3,1,2,3,1]
--
-- @
-- cycled :: 'Fold1' s a -> 'Fold1' s a
-- @
cycled :: Traversal1' s a -> Traversal1' s a
cycled o = wander1 $ \g a -> go g a where go g a = (traverse1Of o g) a .> go g a

{-# INLINE cycled #-}

-- | @x '^.' 'iterated' f@ returns an infinite 'Traversal1'' of repeated applications of @f@ to @x@.
--
-- @
-- 'toListOf' ('iterated' f) a ≡ 'iterate' f a
-- @
--
-- >>> take 3 $ (1 :: Int) ^.. iterated (+1)
-- [1,2,3]
--
-- @
-- iterated :: (a -> a) -> 'Fold1' a a
-- @
iterated :: (a -> a) -> Traversal1' a a
iterated f = wander1 $ \g a0 -> go g a0 where go g a = g a .> go g (f a)
{-# INLINE iterated #-}


---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

traverse1Of :: Apply f => Traversal1 s t a b -> (a -> f b) -> s -> f t
traverse1Of o f = tf where Star tf = o (Star f)

sequence1Of :: Apply f => Traversal1 s t (f a) a -> s -> f t
sequence1Of t = traverse1Of t id

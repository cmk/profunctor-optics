module Data.Profunctor.Optic.Traversal (
    module Data.Profunctor.Optic.Traversal 
  , module Export
) where

import Data.Bitraversable 
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Operator
import Data.Profunctor.Optic.Prelude

import Data.Profunctor.Traversing as Export


---------------------------------------------------------------------
-- Affine Traversal
---------------------------------------------------------------------

{- hedgehog props


affine_complete :: Affine s t a b -> Bool
affine_complete o = tripping o $ affine (match o) (set o)


previewSet :: Eq s => AffineRep s s a a -> s -> Bool
previewSet (AffineRep seta sbt) s = either (\a -> sbt (a, s)) id (seta s) == s

setPreview :: (Eq a, Eq s) => AffineRep s s a a -> a -> s -> Bool
setPreview (AffineRep seta sbt) a s = seta (sbt (a, s)) == either (Left . const a) Right (seta s)

setSet :: Eq s => AffineRep s s a a -> a -> a -> s -> Bool
setSet (AffineRep _ sbt) a1 a2 s = sbt (a2, (sbt (a1, s))) == sbt (a2, s)

affine :: (s -> Either t a)
                -> (s -> b -> t)
                -> Affine s t a b
affine getter setter pab = dimap
    (\s -> (getter s, s))
    (\(bt, s) -> either id (setter s) bt)
    (first' (right' pab))

prism :: (b -> t) -> (s -> Either t a) -> Prism s t a b
prism bt seta = dimap seta (id ||| bt) . right'

lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens sa sbt = dimap (sa &&& id) (uncurry . flip $ sbt) . first'

> affineTraversal :: forall s t a b. (s -> Either t a) -> (s -> b -> t) -> AffineTraversal s t a b
> affineTraversal f g = dimap from (either id (uncurry $ flip g)) . right . first
>  where
>   from :: s -> Either t (a,s)
>   from s = (id +++ (,s)) (f s)

-}

-- sometimes known as a partial lens
affine :: (s -> Either t a) -> (s -> b -> t) -> Affine s t a b
affine seta sbt =
 let f s = (\x -> (x,s)) <$> seta s
     g = id ||| (uncurry . flip $ sbt)

  in dimap f g . right' . first'

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
-- Operators
---------------------------------------------------------------------

sequenceOf
  :: Applicative f
  => Optic (Star f) s t (f a) a -> s -> f t
sequenceOf t = traverseOf t id

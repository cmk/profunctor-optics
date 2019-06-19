{-# LANGUAGE TupleSections #-}


module Data.Profunctor.Optic.Traversal.Affine where

import Data.Bitraversable 
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Operator
import Data.Profunctor.Optic.Prelude


---------------------------------------------------------------------
-- 'Traversal0'
---------------------------------------------------------------------

{- props

more constrained than a Prism b/c we've lost the guaruntee that we
are part of a pure sum type. therefore it cannot be turned around.
 
affine_complete :: Traversal0 s t a b -> Bool
affine_complete o = tripping o $ affine (match o) (set o)


previewSet :: Eq s => Traversal0Rep s s a a -> s -> Bool
previewSet (Traversal0Rep seta sbt) s = either (\a -> sbt (a, s)) id (seta s) == s

setPreview :: (Eq a, Eq s) => Traversal0Rep s s a a -> a -> s -> Bool
setPreview (Traversal0Rep seta sbt) a s = seta (sbt (a, s)) == either (Left . const a) Right (seta s)

setSet :: Eq s => Traversal0Rep s s a a -> a -> a -> s -> Bool
setSet (Traversal0Rep _ sbt) a1 a2 s = sbt (a2, (sbt (a1, s))) == sbt (a2, s)

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

> affineTraversal :: forall s t a b. (s -> Either t a) -> (s -> b -> t) -> Traversal0 s t a b
> affineTraversal f g = dimap from (either id (uncurry $ flip g)) . right . first
>  where
>   from :: s -> Either t (a,s)
>   from s = (id +++ (,s)) (f s)

affine :: Affine s t a b -> Affine s t a b
affine p st = dimap preview dedup . left' . rmap st . first' where
  preview s = either (\a -> Left (a, s)) Right (p s)

-}

-- sometimes known as a partial lens
affine :: (s -> Either t a) -> (s -> b -> t) -> Traversal0 s t a b
affine seta sbt = dimap f g . right' . first'
  where f s = (\x -> (x,s)) <$> seta s
        g = id ||| (uncurry . flip $ sbt)


-- | Obtain a 'Traversal0' that can be composed with to filter another 'Lens', 'Iso', 'View', 'Fold' (or 'Traversal').
--
-- >>> [1..10] ^.. folded . filtered even
-- [2,4,6,8,10]
--
filtered :: (s -> Bool) -> Traversal0' s s
filtered p = affine (\x -> if p x then Right x else Left x) (flip const)
{-# INLINE filtered #-}

selected :: (k -> Bool) -> Traversal0' (k, v) v
selected p = affine (\kv@(k,v) -> if p k then Right v else Left kv) (\kv@(k,_) v' -> if p k then (k,v') else kv)

nulled :: Traversal0' s a
nulled = affine Left const 

---------------------------------------------------------------------
-- Rep
---------------------------------------------------------------------

type ATraversal0 s t a b = Optic (Traversal0Rep a b) s t a b

type ATraversal0' s a = ATraversal0 s s a a


-- | The `Traversal0Rep` profunctor precisely characterizes an 'Traversal0'.
data Traversal0Rep a b s t = Traversal0Rep (s -> Either t a) (s -> b -> t)

idTraversal0Rep :: Traversal0Rep a b a b
idTraversal0Rep = Traversal0Rep Right (\_ -> id)

instance Profunctor (Traversal0Rep u v) where
    dimap f g (Traversal0Rep getter setter) = Traversal0Rep
        (\a -> first g $ getter (f a))
        (\a v -> g (setter (f a) v))

instance Strong (Traversal0Rep u v) where
    first' (Traversal0Rep getter setter) = Traversal0Rep
        (\(a, c) -> first (,c) $ getter a)
        (\(a, c) v -> (setter a v, c))

instance Choice (Traversal0Rep u v) where
    right' (Traversal0Rep getter setter) = Traversal0Rep
        (\eca -> unassoc (second getter eca))
        (\eca v -> second (`setter` v) eca)




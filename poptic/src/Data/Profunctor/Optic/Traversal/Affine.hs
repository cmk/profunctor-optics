{-# LANGUAGE TupleSections #-}


module Data.Profunctor.Optic.Traversal.Affine where

import Data.Bitraversable 
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Operator
import Data.Profunctor.Optic.Prelude


---------------------------------------------------------------------
-- 'Affine' Traversal
---------------------------------------------------------------------

{- hedgehog props

more constrained than a Prism b/c we've lost the guaruntee that we
are part of a pure sum type. therefore it cannot be turned around.
 
affine_complete :: AffineTraversal s t a b -> Bool
affine_complete o = tripping o $ affine (match o) (set o)


previewSet :: Eq s => AffineTraversalRep s s a a -> s -> Bool
previewSet (AffineTraversalRep seta sbt) s = either (\a -> sbt (a, s)) id (seta s) == s

setPreview :: (Eq a, Eq s) => AffineTraversalRep s s a a -> a -> s -> Bool
setPreview (AffineTraversalRep seta sbt) a s = seta (sbt (a, s)) == either (Left . const a) Right (seta s)

setSet :: Eq s => AffineTraversalRep s s a a -> a -> a -> s -> Bool
setSet (AffineTraversalRep _ sbt) a1 a2 s = sbt (a2, (sbt (a1, s))) == sbt (a2, s)

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

affine :: Affine s t a b -> Affine s t a b
affine p st = dimap preview dedup . left' . rmap st . first' where
  preview s = either (\a -> Left (a, s)) Right (p s)

-}

-- sometimes known as a partial lens
affine :: (s -> Either t a) -> (s -> b -> t) -> AffineTraversal s t a b
affine seta sbt =
 let f s = (\x -> (x,s)) <$> seta s
     g = id ||| (uncurry . flip $ sbt)

  in dimap f g . right' . first'

-- | When you see this as an argument to a function, it expects an 'Affine'.
type AnAffineTraversal s t a b = Optic (AffineTraversalRep a b) s t a b

type AnAffineTraversal' s a = AnAffineTraversal s s a a


--selecting :: (k -> Bool) -> AffineTraversal' (k, v) v
--selecting p =  affine (\kv@(k,v) -> if (p k) then Right v else Left kv) (\v' kv@(k,_) -> if (p k) then (k,v') else kv)

null :: AffineTraversal' s a
null = affine Left const 

---------------------------------------------------------------------
-- 
---------------------------------------------------------------------

-- | The `AffineTraversalRep` profunctor precisely characterizes an 'AffineTraversal'.
data AffineTraversalRep a b s t = AffineTraversalRep (s -> Either t a) (s -> b -> t)

idAffineTraversalRep :: AffineTraversalRep a b a b
idAffineTraversalRep = AffineTraversalRep Right (\_ -> id)

instance Profunctor (AffineTraversalRep u v) where
    dimap f g (AffineTraversalRep getter setter) = AffineTraversalRep
        (\a -> first g $ getter (f a))
        (\a v -> g (setter (f a) v))

instance Strong (AffineTraversalRep u v) where
    first' (AffineTraversalRep getter setter) = AffineTraversalRep
        (\(a, c) -> first (,c) $ getter a)
        (\(a, c) v -> (setter a v, c))

instance Choice (AffineTraversalRep u v) where
    right' (AffineTraversalRep getter setter) = AffineTraversalRep
        (\eca -> unassoc (second getter eca))
        (\eca v -> second (`setter` v) eca)




module Data.Profunctor.Optic.Affine where

import Control.Arrow ((|||))
import Data.Profunctor
import Data.Profunctor.Optic.Type

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

foo :: Affine (Either c1 (a, c2)) (Either c1 (b, c2)) a b
foo = right' . first'


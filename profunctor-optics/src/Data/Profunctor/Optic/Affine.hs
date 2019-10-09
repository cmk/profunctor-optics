{-# LANGUAGE TupleSections #-}


module Data.Profunctor.Optic.Affine where

import Data.Bitraversable 
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Prelude

import Data.Profunctor.Optic.Prism

import Data.Maybe (fromMaybe)

---------------------------------------------------------------------
-- 'Affine'
---------------------------------------------------------------------

{- props

more constrained than a Prism b/c we've lost the guaruntee that we
are part of a pure sum type. therefore it cannot be turned around.
 
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

> affineTraversal :: forall s t a b. (s -> Either t a) -> (s -> b -> t) -> Affine s t a b
> affineTraversal f g = dimap from (either id (uncurry $ flip g)) . right . first
>  where
>   from :: s -> Either t (a,s)
>   from s = (id +++ (,s)) (f s)

affine :: Affine s t a b -> Affine s t a b
affine p st = dimap preview dedup . left' . rmap st . first' where
  preview s = either (\a -> Left (a, s)) Right (p s)

-}

-- | Create a 'Affine'' from a constructor and a matcher function that
-- produces an 'Either'.
affine :: (s -> Either t a) -> (s -> b -> t) -> Affine s t a b
affine seta sbt = dimap f g . right' . first'
  where f s = (\x -> (x,s)) <$> seta s
        g = id ||| (uncurry . flip $ sbt)

-- | Create a 'Affine'' from a constructor and a matcher function that
-- produces a 'Maybe'.
affine' :: (s -> Maybe a) -> (s -> a -> s) -> Affine' s a
affine' sma sas = flip affine sas $ \s -> maybe (Left s) Right (sma s)


{-
-- | Obtain a 'Affine' that can be composed with to filter another 'Lens', 'Iso', 'Getter', 'Fold' (or 'Traversal').
--
-- >>> [1..10] ^.. folded . filtering even
-- [2,4,6,8,10]
--
filtered :: (s -> Bool) -> Affine' s s
filtered p = affine (branch' p) (flip const)
{-# INLINE filtered #-}

catMaybes = undefined :: f (Maybe a) -> f a
mapMaybe :: (a -> Maybe b) -> f a -> f b
whenLeft :: Applicative f => (a -> Maybe x) -> Either a c -> f ()


selectA :: Applicative f => f (Either a b) -> f (a -> b) -> f b
selectA x y = (\e f -> either f id e) <$> x <*> y

-- | A lifted version of 'Data.Maybe.fromMaybe'.
fromMaybeA :: Applicative f => f a -> f (Maybe a) -> f a
fromMaybeA x mx = selectA (maybe (Left ()) Right <$> mx) (const <$> x)


catMaybes :: Alternative f => f (Maybe a) -> f a
catMaybes = fromMaybeA empty

fromMaybeS = undefined :: f a -> f (Maybe a) -> f a

-- | A lifted version of 'Data.Maybe.fromMaybe'.
fromMaybeS :: Selective f => f a -> f (Maybe a) -> f a
fromMaybeS x mx = select (maybe (Left ()) Right <$> mx) (const <$> x)

catMaybes :: (Selective f, Alternative f) => f (Maybe a) -> f a
catMaybes = fromMaybeS empty

mapMaybe :: (Selective f, Alternative f) => (a1 -> Maybe a2) -> f a1 -> f a2
mapMaybe f = catMaybes . fmap f

\amb fa -> maybe (Left ()) Right <$> fmap amb fa


foo :: Alternative f => (s -> Maybe a) -> s -> Either (f t) a
foo sma s = maybe (Left empty) Right $ sma s

pfoo :: Alternative f => (s -> Maybe a) -> Prism s (f t) a (f (Maybe t))
pfoo f = prism (foo f) catMaybes


afoo :: Alternative f => (f s -> Maybe a) -> Affine (f s) (f s) a (f (Maybe s))
afoo f = affine (foo f) fromMaybeS

mapMaybe sma = affine' sma fromMaybe

-}
selected :: (k -> Bool) -> Affine' (k, v) v
selected p = affine (\kv@(k,v) -> branch p kv v k) (\kv@(k,_) v' -> if p k then (k,v') else kv)

nulled :: Affine' s a
nulled = affine Left const 


---------------------------------------------------------------------
-- 'AffineRep'
---------------------------------------------------------------------

-- | The `AffineRep` profunctor precisely characterizes an 'Affine'.
data AffineRep a b s t = AffineRep (s -> Either t a) (s -> b -> t)

idAffineRep :: AffineRep a b a b
idAffineRep = AffineRep Right (\_ -> id)

instance Profunctor (AffineRep u v) where
    dimap f g (AffineRep getter setter) = AffineRep
        (\a -> first g $ getter (f a))
        (\a v -> g (setter (f a) v))

instance Strong (AffineRep u v) where
    first' (AffineRep getter setter) = AffineRep
        (\(a, c) -> first (,c) $ getter a)
        (\(a, c) v -> (setter a v, c))

instance Choice (AffineRep u v) where
    right' (AffineRep getter setter) = AffineRep
        (\eca -> unassoc (second getter eca))
        (\eca v -> second (`setter` v) eca)

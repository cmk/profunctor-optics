module Data.Profunctor.Optic.Prism where

import Control.Arrow ((|||))
import Control.Monad (guard)
import Data.Profunctor.Optic.Types -- (APrism, APrism', Prism, Prism', Review, under)
import Data.Profunctor.Optic.Operators

{- hedgehog rules:

prism_complete :: Prism s t a b -> Prism s t a b
prism_complete p = prism (preview p) (matching p)

They have two operations: match and build. The first one tries to extract the focus value from the whole one, but if it's not possible, it provides the final value for t. On the other hand, build is always able to construct the whole value, given the focus one. As expected, this optic should hold the following properties.

-- If we are able to view an existing focus, then building it will return the original structure. 
matchBuild :: Eq s => Prism_ s s a a -> s -> Bool
matchBuild (Prism_ seta bt) s = either bt id (seta s) == s

-- If we build a whole from any focus, that whole must contain a focus.
buildMatch :: (Eq a, Eq s) => Prism_ s s a a -> a -> Bool
buildMatch (Prism_ seta bt) a = seta (bt a) == Left a --Right a ?


maybeFirst :: Affine (Maybe a, c) (Maybe b, c) a b
maybeFirst = Affine p st where
  p (ma, c) = maybe (Right (Nothing, c)) Left ma
  st (b, (ma, c)) = (ma $> b, c)

λ> preview maybeFirst (Just 1, "hi")
Left 1
λ> preview maybeFirst (Nothing, "hi")
Right (Nothing,"hi")
λ> set maybeFirst ('a', (Just 1, "hi"))
(Just 'a',"hi")
λ> set maybeFirst ('a', (Nothing, "hi"))
(Nothing,"hi")
-}




-- | Create a 'Prism' from a constructor and a matcher function that
-- | produces an 'Either'.
prism :: (b -> t) -> (s -> Either t a) -> Prism s t a b
prism bt seta = dimap seta (id ||| bt) . right'


-- | Create a `Prism` from a constructor and a matcher function that
-- | produces a `Maybe`.
prism' :: (a -> s) -> (s -> Maybe a) -> Prism' s a
prism' as sma = prism as (\s -> maybe (Left s) Right (sma s))

-- Useful for constructing Prefs from handle and try functions.
eprism :: (Either e b -> t) -> (s -> Either e a) -> Prism s t a b
eprism build match = dimap match build . right'

clonePrism :: APrism s t a b -> Prism s t a b
clonePrism l = withPrism l $ \x y p -> prism x y p


withPrism :: APrism s t a b -> ((b -> t) -> (s -> Either t a) -> r) -> r
withPrism l f = case l (Prism_ id Right) of
  Prism_ g h -> f g h


matching'' :: APrism s t a b -> s -> Either t a
matching'' l = withPrism l $ \_ f -> f

-- | Ask if 'preview' would produce a 'Just' on this prism.
is :: APrism s t a b -> s -> Bool
is l = either (const False) (const True) . matching'' l


-- | Ask if 'preview' would produce a 'Nothing' on this prism.
isnt :: APrism s t a b -> s -> Bool
isnt l = not . is l


-- | Create a 'Prism' from a value and a predicate.
nearly ::  a -> (a -> Bool) -> Prism' a ()
nearly x f = prism' (const x) (guard . f)


-- | 'only' focuses not just on a case, but a specific value of that case.
only :: Eq a => a -> Prism a a () ()
only x = nearly x (x==)


-- | Use a 'Prism' to work over part of a structure.
--
aside :: APrism s t a b -> Prism (e, s) (e, t) (e, a) (e, b)
aside k =
  withPrism k $ \bt seta ->
    prism (fmap bt) $ \(e,s) ->
      case seta s of
        Left t  -> Left  (e,t)
        Right a -> Right (e,a)
{-# INLINE aside #-}


-- | Given a pair of prisms, project sums.
--
-- Viewing a 'Prism' as a co-'Lens', this combinator can be seen to be dual to 'Control.Lens.Lens.alongside'.
without :: APrism s t a b
        -> APrism u v c d
        -> Prism (Either s u) (Either t v) (Either a c) (Either b d)
without k =
  withPrism k $ \bt seta k' ->
    withPrism k' $ \dv uevc ->
      prism (bimap bt dv) $ \su ->
        case su of
          Left s  -> bimap Left Left (seta s)
          Right u -> bimap Right Right (uevc u)
{-# INLINE without #-}



-- | 'lift' a 'Prism' through a 'Traversable' functor, giving a Prism that matches only if all the elements of the container match the 'Prism'.
--
-- >>> [Left 1, Right "foo", Left 4, Right "woot"]^..below _Right
-- []
--
-- >>> [Right "hail hydra!", Right "foo", Right "blah", Right "woot"]^..below _Right
-- [["hail hydra!","foo","blah","woot"]]
below :: Traversable f => APrism' s a -> Prism' (f s) (f a)
below k =
  withPrism k $ \bt seta ->
    prism (fmap bt) $ \s ->
      case traverse seta s of
        Left _  -> Left s
        Right t -> Right t
{-# INLINE below #-}


{-
-- | Use a 'Prism' as a kind of first-class pattern.
--
-- @'outside' :: 'Prism' s t a b -> 'Lens' (t -> r) (s -> r) (b -> r) (a -> r)@

-- TODO: can we make this work with merely Strong?
outside :: Representable p => APrism s t a b -> Lens (p t r) (p s r) (p b r) (p a r)
outside k = withPrism k $ \bt seta f ft ->
  f (lmap bt ft) <&> \fa -> tabulate $ either (sieve ft) (sieve fa) . seta
{-# INLINE outside #-}


-}

-- | Prism for the `Nothing` constructor of `Maybe`.
_Nothing :: Prism (Maybe a) (Maybe b) () ()
_Nothing = prism (const Nothing) $ maybe (Right ()) (const $ Left Nothing)


-- | Prism for the `Just` constructor of `Maybe`.
_Just :: Prism (Maybe a) (Maybe b) a b
_Just = prism Just $ maybe (Left Nothing) Right


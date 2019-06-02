module Data.Profunctor.Optic.Prism (
    module Data.Profunctor.Optic.Prism 
  , module Export
) where

import Control.Monad (guard)
import Data.Profunctor.Optic.Prelude 
import Data.Profunctor.Optic.Type -- (APrism, APrism', Prism, Prism', Review, under)
import Data.Profunctor.Optic.Operator
import Data.Either.Validation (Validation(..), eitherToValidation, validationToEither)


import Data.Profunctor.Choice as Export

{- prism laws:

Prism is the characterization of a Choice profunctor. It identifies 
objects as consisting of a sum of two components.

prism_complete :: Prism s t a b -> Bool
prism_complete p = tripping p $ prism (preview p) (matching p)

They have two operations: match and build. The first one tries to extract the focus value from the whole one, but if it's not possible, it provides the final value for t. On the other hand, build is always able to construct the whole value, given the focus one. As expected, this optic should hold the following properties.

-- If we are able to view an existing focus, then building it will return the original structure. 
matchBuild :: Eq s => PrismRep s s a a -> s -> Bool
matchBuild (PrismRep seta bt) s = either bt id (seta s) == s

-- If we build a whole from any focus, that whole must contain a focus.
buildMatch :: (Eq a, Eq s) => PrismRep s s a a -> a -> Bool
buildMatch (PrismRep seta bt) a = seta (bt a) == Left a --Right a ?

First, if I review a value with a Prism and then preview, I will get it back:

preview l (review l b) ≡ Just b

If you can extract a value a using a Prism l from a value s, then the value s is completely described by l and a:
preview l s ≡ Just a ⇒ review l a ≡ s


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
prism bt seta = dimap seta (id ||| bt) . _Right

-- | Create a `Prism` from a constructor and a matcher function that
-- | produces a `Maybe`.
prism' :: (a -> s) -> (s -> Maybe a) -> Prism' s a
prism' as sma = prism as (\s -> maybe (Left s) Right (sma s))

-- | 'Validation' is isomorphic to 'Either'
_Validation :: Iso (Validation e a) (Validation g b) (Either e a) (Either g b)
_Validation = dimap validationToEither eitherToValidation
{-# INLINE _Validation #-}


-- | Useful for constructing prisms from try and handle functions.
handled :: (Either e b -> t) -> (s -> Either e a) -> Prism s t a b
handled eebt seea = dimap seea eebt . _Right

validated :: (Validation e b -> t) -> (s -> Validation e a) -> Prism s t a b
validated vebt svea = dimap svea vebt . dimap validationToEither eitherToValidation . _Right

-- | Analogous to '(+++)' from 'Control.Arrow'
(+|+) :: Prism s t a b -> Prism s' t' a' b' -> Prism (Either s s') (Either t t') (Either a a') (Either b b') 
(+|+) = split

prismOf
  :: Choice p 
  => (b -> t)
  -> (s -> Either t a)
  -> Optic p (Either c s) (Either d t) (Either c a) (Either d b)
prismOf f g = between runSplit Split (prism f g)

clonePrism :: APrism s t a b -> Prism s t a b
clonePrism l = withPrism l $ \x y p -> prism x y p

withPrism :: APrism s t a b -> ((b -> t) -> (s -> Either t a) -> r) -> r
withPrism l f = case l (PrismRep id Right) of PrismRep g h -> f g h

---------------------------------------------------------------------
-- 
---------------------------------------------------------------------


-- | The 'PrismRep' profunctor precisely characterizes a 'Prism'.
data PrismRep a b s t = PrismRep (b -> t) (s -> Either t a)

instance Functor (PrismRep a b s) where

  fmap f (PrismRep bt seta) = PrismRep (f . bt) (either (Left . f) Right . seta)
  {-# INLINE fmap #-}

instance Profunctor (PrismRep a b) where

  dimap f g (PrismRep bt seta) = PrismRep (g . bt) $
    either (Left . g) Right . seta . f
  {-# INLINE dimap #-}

  lmap f (PrismRep bt seta) = PrismRep bt (seta . f)
  {-# INLINE lmap #-}

  rmap f (PrismRep bt seta) = PrismRep (f . bt) (either (Left . f) Right . seta)
  {-# INLINE rmap #-}

instance Choice (PrismRep a b) where

  left' (PrismRep bt seta) = PrismRep (Left . bt) $ 
    either (either (Left . Left) Right . seta) (Left . Right)
  {-# INLINE left' #-}

  right' (PrismRep bt seta) = PrismRep (Right . bt) $ 
    either (Left . Left) (either (Left . Right) Right . seta)
  {-# INLINE right' #-}


type APrism s t a b = Optic (PrismRep a b) s t a b

-- | When you see this as an argument to a function, it expects a 'Prism'.
type APrism' s a = APrism s s a a

---------------------------------------------------------------------
-- Common prisms
---------------------------------------------------------------------

filtering :: (a -> Bool) -> Prism a a a a
filtering p = dimap getter (either id id) . _Right 
  where
    getter x | p x       = Right x
             | otherwise = Left x

-- | Filters on a predicate.
filtered :: (a -> Bool) -> Prism (Either c a) (Either c b) (Either a a) (Either b b)
filtered f = _Right . dimap (\x -> if f x then Right x else Left x) (either id id)

binding :: Eq k => k -> Prism' (k, v) v
binding i = prism ((,) i) (\kv@(k,v) -> if (i == k) then Right v else Left kv) 

-- | Create a 'Prism' from a value and a predicate.
nearly ::  a -> (a -> Bool) -> Prism' a ()
nearly x f = prism' (const x) (guard . f)

-- | 'only' focuses not just on a case, but a specific value of that case.
only :: Eq a => a -> Prism a a () ()
only x = nearly x (x==)

-- | Prism for the `Nothing` constructor of `Maybe`.
_Nothing :: Prism (Maybe a) (Maybe b) () ()
_Nothing = prism (const Nothing) $ maybe (Right ()) (const $ Left Nothing)

-- | Prism for the `Just` constructor of `Maybe`.
_Just :: Prism (Maybe a) (Maybe b) a b
_Just = prism Just $ maybe (Left Nothing) Right

_Left :: Prism (Either a c) (Either b c) a b
_Left = left'

_Right :: Prism (Either c a) (Either c b) a b
_Right = right'


-- | dimap v2e e2v . left' == prism Failure $ validation Right (Left . Success)
_Failure :: Prism (Validation a c) (Validation b c) a b
_Failure = dimap v2e e2v . left'
{-# INLINE _Failure #-}


-- | prism dimap v2e e2v . right' == Success $ validation (Left . Failure) Right
_Success :: Prism (Validation c a) (Validation c b) a b
_Success = dimap v2e e2v . right'
{-# INLINE _Success #-}


-- | 'lift' a 'Prism' through a 'Traversable' functor, 
-- giving a Prism that matches only if all the elements of the container
-- match the 'Prism'.
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


-- | Use a 'Prism' to work over part of a structure.
aside :: APrism s t a b -> Prism (e, s) (e, t) (e, a) (e, b)
aside k =
  withPrism k $ \bt seta ->
    prism (fmap bt) $ \(e,s) ->
      case seta s of
        Left t  -> Left  (e,t)
        Right a -> Right (e,a)
{-# INLINE aside #-}

-- | Given a pair of prisms, project sums.
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


---------------------------------------------------------------------
-- Derived operators
---------------------------------------------------------------------

-- | Test whether the optic matches or not.
is :: Matching a s t a b -> s -> Bool
is o = either (const False) (const True) . match o

-- | Test whether the optic matches or not.
isnt :: Matching a s t a b -> s -> Bool
isnt o = not . is o

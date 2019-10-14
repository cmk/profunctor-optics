module Data.Profunctor.Optic.Prism where

import Control.Monad (guard)
import Data.Profunctor.Optic.Prelude 
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Iso

---------------------------------------------------------------------
-- 'Prism'
---------------------------------------------------------------------

{- prism laws:

Prism is the characterization of a Choice profunctor. It identifies 
objects as consisting of a sum of two components.

prism_complete :: Prism s t a b -> Bool
prism_complete p = tripping p $ prism (preview p) (matching p)

They have two operations: matchOf and build. The first one tries to extract the focus value from the whole one, but if it's not possible, it provides the final value for t. On the other hand, build is always able to construct the whole value, given the focus one. As expected, this optic should hold the following properties.

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


-- | Build a 'Choice' optic from a constructor and a matcher function.
--
-- /Caution/: In order for the generated prism family to be well-defined,
-- you must ensure that the three prism laws hold:
--
-- * @seta (bt b) === Right b@
--
-- * @(id ||| bt) (seta s) === s@
--
-- * @left seta (seta s) === left Left (seta s)@
--
prism :: (s -> t + a) -> (b -> t) -> Prism s t a b
prism seta bt = dimap seta (id ||| bt) . right'

-- | Build a 'Cochoice' optic from a constructor and a matcher function.
--
-- * @coprism f g === \f g -> re (prism f g)@
--
coprism :: (s -> t + a) -> (b -> t) -> Coprism b a t s
coprism seta bt = unright . dimap (id ||| bt) seta

-- | Create a 'Prism' from a reviewer and a matcher function that produces a 'Maybe'.
--
prism' :: (s -> Maybe a) -> (a -> s) -> Prism' s a
prism' sma as = flip prism as $ \s -> maybe (Left s) Right (sma s)

-- | Transform a Van Laarhoven-encoded prism into a profunctor-encoded one.
--
--prismvl :: (forall f. Applicative f => Traversable g => (g a -> f b) -> g s -> f t) -> Prism s t a b
--prismvl l = undefined 

--prismek :: (forall f p. Applicative f => Choice p => (p a (f b) -> p s (f t)) -> Prism s t a b
--prismek l = undefined 

-- | Useful for constructing prisms from try and handle functions.
--
handled ::  (s -> e + a) -> (e + b -> t) -> Prism s t a b
handled sea ebt = dimap sea ebt . right'

-- | Analogous to '(+++)' from 'Control.Arrow'
splitting' :: Prism s t a b -> Prism s' t' a' b' -> Prism (s+s') (t+t') (a+a') (b+b') 
splitting' = split

prismR
  :: Choice p 
  => (s -> t + a)
  -> (b -> t)
  -> Optic p (c + s) (d + t) (c + a) (d + b)
prismR f g = between runSplit Split (prism f g)

withPrism :: APrism s t a b -> ((s -> t + a) -> (b -> t) -> r) -> r
withPrism l f = case l (PrismRep Right id) of PrismRep g h -> f g h

clonePrism :: APrism s t a b -> Prism s t a b
clonePrism l = withPrism l $ \x y p -> prism x y p

-- | 'lift' a 'Prism' through a 'Traversable' functor, 
-- giving a Prism that matches only if all the elements of the container
-- matchOf the 'Prism'.
--
-- >>> [Left 1, Right "foo", Left 4, Right "woot"]^..below _R
-- []
--
-- >>> [Right "hail hydra!", Right "foo", Right "blah", Right "woot"]^..below _R
-- [["hail hydra!","foo","blah","woot"]]
below :: Traversable f => APrism' s a -> Prism' (f s) (f a)
below k =
  withPrism k $ \seta bt ->
    flip prism (fmap bt) $ \s ->
      case traverse seta s of
        Left _  -> Left s
        Right t -> Right t
{-# INLINE below #-}

-- | Use a 'Prism' to work lift part of a structure.
aside :: APrism s t a b -> Prism (e , s) (e , t) (e , a) (e , b)
aside k =
  withPrism k $ \seta bt ->
    flip prism (fmap bt) $ \(e,s) ->
      case seta s of
        Left t  -> Left  (e,t)
        Right a -> Right (e,a)
{-# INLINE aside #-}

-- | Given a pair of prisms, project sums.
without :: APrism s t a b
        -> APrism u v c d
        -> Prism (s + u) (t + v) (a + c) (b + d)
without k =
  withPrism k $ \seta bt k' ->
    withPrism k' $ \uevc dv ->
      flip prism (bimap bt dv) $ \su ->
        case su of
          Left s  -> bimap Left Left (seta s)
          Right u -> bimap Right Right (uevc u)
{-# INLINE without #-}

---------------------------------------------------------------------
-- 'PrismRep'
---------------------------------------------------------------------

type APrism s t a b = Optic (PrismRep a b) s t a b

type APrism' s a = APrism s s a a

type AMatch e s t a b = LensLike (Either e) s t a b

-- | The 'PrismRep' profunctor precisely characterizes a 'Prism'.
data PrismRep a b s t = PrismRep (s -> Either t a) (b -> t)

instance Functor (PrismRep a b s) where

  fmap f (PrismRep seta bt) = PrismRep (either (Left . f) Right . seta) (f . bt)
  {-# INLINE fmap #-}

instance Profunctor (PrismRep a b) where

  dimap f g (PrismRep seta bt) = PrismRep (either (Left . g) Right . seta . f) (g . bt)
  {-# INLINE dimap #-}

  lmap f (PrismRep seta bt) = PrismRep (seta . f) bt
  {-# INLINE lmap #-}

  rmap f (PrismRep seta bt) = PrismRep (either (Left . f) Right . seta) (f . bt)
  {-# INLINE rmap #-}

instance Choice (PrismRep a b) where

  left' (PrismRep seta bt) = PrismRep (either (either (Left . Left) Right . seta) (Left . Right)) (Left . bt)
  {-# INLINE left' #-}

  right' (PrismRep seta bt) = PrismRep (either (Left . Left) (either (Left . Right) Right . seta)) (Right . bt)
  {-# INLINE right' #-}

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- ^ @
-- matchOf :: Affine s t a b -> s -> Either t a
-- matchOf :: Traversal s t a b -> s -> Either t a
-- @
--
matchOf :: AMatch a s t a b -> s -> Either t a
matchOf o = between (dstar coswp) (ustar Left) o id

-- | Test whether the optic matches or not.
isMatched :: AMatch a s t a b -> s -> Bool
isMatched o = either (const False) (const True) . matchOf o

-- | Test whether the optic matches or not.
isntMatched :: AMatch a s t a b -> s -> Bool
isntMatched o = not . isMatched o

---------------------------------------------------------------------
-- Common prisms
---------------------------------------------------------------------

-- | TODO: Document
--
_L :: Prism (a + c) (b + c) a b
_L = left'

-- | TODO: Document
--
_R :: Prism (c + a) (c + b) a b
_R = right'

-- | TODO: Document
--
lowerL :: Iso s t (a + c) (b + c) -> Prism s t a b
lowerL = (. _L)

-- | TODO: Document
--
lowerR :: Iso s t (c + a) (c + b) -> Prism s t a b
lowerR = (. _R)

-- | Obtain a 'Prism' that can be composed with to filter another 'Lens', 'Iso', 'Getter', 'Fold' (or 'Traversal').
--
-- >>> [1..10] ^.. folded . filtered even
-- [2,4,6,8,10]
--
filtered :: (a -> Bool) -> Prism' a a
filtered f = iso (branch' f) dedup . _R 

-- | TODO: Document
--
selected :: Eq k => k -> Prism' (k , v) v
selected i = flip prism ((,) i) $ \kv@(k,v) -> branch (==i) kv v k

-- | Create a 'Prism' from a value and a predicate.
nearly ::  a -> (a -> Bool) -> Prism' a ()
nearly x f = prism' (guard . f) (const x)

-- | 'only' focuses not just on a case, but a specific value of that case.
only :: Eq a => a -> Prism' a ()
only x = nearly x (x==)

lessThan :: Bounded s => Ord s => s -> Prism' s Ordering
lessThan s = flip prism' (const s) $ \s' -> if s' < s then Just LT else Nothing  

-- | Prism for the `Just` constructor of `Maybe`.
_Just :: Prism (Maybe a) (Maybe b) a b
_Just = flip prism Just $ maybe (Left Nothing) Right

-- | Prism for the `Nothing` constructor of `Maybe`.
_Nothing :: Prism (Maybe a) (Maybe b) () ()
_Nothing = flip prism  (const Nothing) $ maybe (Right ()) (const $ Left Nothing)

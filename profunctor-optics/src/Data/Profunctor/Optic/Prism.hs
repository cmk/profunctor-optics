module Data.Profunctor.Optic.Prism where

import Control.Monad (guard)
import Data.Profunctor.Optic.Prelude 
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Iso

---------------------------------------------------------------------
-- 'Prism'
---------------------------------------------------------------------

-- | Build a 'Choice' optic from a constructor and a matcher function.
--
-- \( \quad \mathsf{Prism}\;S\;A = \exists D, S \cong D + A \)
--
-- /Caution/: In order for the generated prism family to be well-defined,
-- you must ensure that the three prism laws hold:
--
-- * @seta (bt b) ≡ Right b@
--
-- * @(id ||| bt) (seta s) ≡ s@
--
-- * @left seta (seta s) ≡ left Left (seta s)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
prism :: (s -> t + a) -> (b -> t) -> Prism s t a b
prism seta bt = dimap seta (id ||| bt) . pright

-- | Create a 'Prism' from a reviewer and a matcher function that produces a 'Maybe'.
--
prism' :: (s -> Maybe a) -> (a -> s) -> Prism' s a
prism' sma as = flip prism as $ \s -> maybe (Left s) Right (sma s)

-- | Build a 'Cochoice' optic from a constructor and a matcher function.
--
-- * @coprism f g ≡ \f g -> re (prism f g)@
--
coprism :: (s -> t + a) -> (b -> t) -> Coprism b a t s
coprism seta bt = unright . dimap (id ||| bt) seta

-- | Transform a Van Laarhoven-encoded prism into a profunctor-encoded one.
--
--prismvl :: (forall f. Applicative f => Traversable g => (g a -> f b) -> g s -> f t) -> Prism s t a b
--prismvl l = undefined 

--prismek :: (forall f p. Applicative f => Choice p => (p a (f b) -> p s (f t)) -> Prism s t a b
--prismek l = undefined 

-- | Build a 'Prism' from its free tensor representation.
--
-- Useful for constructing prisms from try and handle functions.
--
handled :: (s -> e + a) -> (e + b -> t) -> Prism s t a b
handled sea ebt = dimap sea ebt . pright

clonePrism :: APrism s t a b -> Prism s t a b
clonePrism o = withPrism o prism

---------------------------------------------------------------------
-- 'PrismRep'
---------------------------------------------------------------------

type APrism s t a b = Optic (PrismRep a b) s t a b

type APrism' s a = APrism s s a a

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

withPrism :: APrism s t a b -> ((s -> t + a) -> (b -> t) -> r) -> r
withPrism o f = case o (PrismRep Right id) of PrismRep g h -> f g h

-- | Analogous to @(+++)@ from 'Control.Arrow'
--
splitting :: Prism s1 t1 a1 b1 -> Prism s2 t2 a2 b2 -> Prism (s1 + s2) (t1 + t2) (a1 + a2) (b1 + b2) 
splitting = split

prismr :: (s -> t + a) -> (b -> t) -> Prism (c + s) (d + t) (c + a) (d + b)
prismr f g = between runSplit Split (prism f g)

-- | Use a 'Prism' to lift part of a structure.
--
aside :: APrism s t a b -> Prism (e , s) (e , t) (e , a) (e , b)
aside k =
  withPrism k $ \seta bt ->
    flip prism (fmap bt) $ \(e,s) ->
      case seta s of
        Left t  -> Left  (e,t)
        Right a -> Right (e,a)
{-# INLINE aside #-}

-- | Given a pair of prisms, project sums.
without :: APrism s t a b -> APrism u v c d -> Prism (s + u) (t + v) (a + c) (b + d)
without k =
  withPrism k $ \seta bt k' ->
    withPrism k' $ \uevc dv ->
      flip prism (bimap bt dv) $ \su ->
        case su of
          Left s  -> bimap Left Left (seta s)
          Right u -> bimap Right Right (uevc u)
{-# INLINE without #-}

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

---------------------------------------------------------------------
-- Common prisms
---------------------------------------------------------------------

-- | TODO: Document
--
_L :: Prism (a + c) (b + c) a b
_L = pleft

-- | TODO: Document
--
_R :: Prism (c + a) (c + b) a b
_R = pright

-- | TODO: Document
--
lowerL :: Iso s t (a + c) (b + c) -> Prism s t a b
lowerL = (. _L)

-- | TODO: Document
--
lowerR :: Iso s t (c + a) (c + b) -> Prism s t a b
lowerR = (. _R)

-- | Obtain a 'Prism' that can be composed with to filter another 'Lens', 'Iso', 'View', 'Fold' (or 'Traversal').
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

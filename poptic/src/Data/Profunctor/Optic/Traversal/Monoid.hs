{-# LANGUAGE TupleSections #-}
module Data.Profunctor.Optic.Traversal.Monoid (
    module Export
  , module Data.Profunctor.Optic.Traversal.Monoid
) where

import Data.Bitraversable 
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Operator
import Data.Profunctor.Optic.Prelude

import Data.Profunctor.Traversing                as Export

import Data.Traversable (fmapDefault, foldMapDefault)

---------------------------------------------------------------------
-- 'Traversal'
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

{-
The laws for a 'Traversal' follow from the laws for 'Traversable' as stated in "The Essence of the Iterator Pattern".

Identity:

traverseOf t (Identity . f) ≡  Identity (fmap f)

Composition:

Compose . fmap (traverseOf t f) . traverseOf t g == traverseOf t (Compose . fmap f . g)

One consequence of this requirement is that a 'Traversal' needs to leave the same number of elements as a
candidate for subsequent 'Traversal' that it started with. 

-}
-- ^ @
-- traverseOf :: Functor f => Lens s t a b -> (a -> f b) -> s -> f t
-- traverseOf :: Applicative f => Traversal s t a b -> (a -> f b) -> s -> f t
-- traverseOf $ _1 . _R :: Applicative f => (a -> f b) -> (Either c a, d) -> f (Either c b, d)
-- traverseOf == between runStar Star 
-- @

traverseOf :: ATraversal f s t a b -> (a -> f b) -> s -> f t
traverseOf o f = tf where Star tf = o (Star f)

sequenceOf :: Applicative f => ATraversal f s t (f a) a -> s -> f t
sequenceOf t = traverseOf t id

traversalVL :: (forall f. Applicative f => (a -> f b) -> s -> f t) -> Traversal s t a b
traversalVL l = dimap f g . traverse'
 where
  f ta = TraversableFreeApplicativePStore (FreeApplicativePStore (flip l ta))
  g (TraversableFreeApplicativePStore (FreeApplicativePStore fps)) = runIdentity (fps Identity)


newtype FreeApplicativePStore i j x = FreeApplicativePStore { runFreeApplicativePStore :: forall f. Applicative f => (i -> f j) -> f x }

instance Functor (FreeApplicativePStore i j) where
  fmap f (FreeApplicativePStore fps) = FreeApplicativePStore $ (fmap f) . fps

instance Applicative (FreeApplicativePStore i j) where
  pure x = FreeApplicativePStore $ const (pure x)
  FreeApplicativePStore f <*> FreeApplicativePStore x = FreeApplicativePStore $ \op -> (f op) <*> (x op)

idFreeApplicativePStore :: a -> FreeApplicativePStore a b b
idFreeApplicativePStore a = FreeApplicativePStore ($ a)

newtype TraversableFreeApplicativePStore j x i = TraversableFreeApplicativePStore { getTraversableFreeApplicativePStore :: FreeApplicativePStore i j x }

instance Functor (TraversableFreeApplicativePStore j x) where
  fmap = fmapDefault

instance Foldable (TraversableFreeApplicativePStore j x) where
  foldMap = foldMapDefault

instance Traversable (TraversableFreeApplicativePStore j x) where
  traverse f (TraversableFreeApplicativePStore (FreeApplicativePStore fps)) = fmap TraversableFreeApplicativePStore . getCompose $
    fps (Compose . fmap idFreeApplicativePStore . f)

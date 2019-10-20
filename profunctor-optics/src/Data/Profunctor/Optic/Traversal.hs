{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GADTs, DeriveFunctor #-}

module Data.Profunctor.Optic.Traversal where

import Data.Bitraversable 
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Prelude-- ((+), dup, dedup, swp, coswp, apply)

import Data.Traversable (fmapDefault, foldMapDefault)

--import Data.Profunctor.Task
import Data.Profunctor.Choice
import Data.Profunctor.Monad
import Data.Profunctor.Strong
import Control.Applicative.Free.Fast
import Data.Functor.Identity
import Data.Profunctor.Types
import Data.Profunctor.Unsafe

import qualified Data.Tuple as T
import Prelude hiding (mapM, id, (.))
--import Control.Category
--import Control.Arrow 
import qualified Control.Category as C
import qualified Control.Arrow as A
import Data.Foldable (traverse_)

---------------------------------------------------------------------
-- 'Traversal'
---------------------------------------------------------------------

-- | TODO: Document, DList
--
traversing :: Traversable f => (s -> f a) -> (s -> f b -> t) -> Traversal s t a b
traversing sa sbt = dimap dup (uncurry sbt) . second' . lmap sa . wander traverse

-- | TODO: Document
--
traversed :: Traversable f => Traversal (f a) (f b) a b
traversed = wander traverse

-- | Traverse both parts of a 'Bitraversable' container with matching types.
--
-- >>> traverseOf both (pure . length) (Right "hello")
-- Right 5
--
-- >>> traverseOf both (pure . length) ("hello","world")
-- (5,5)
--
-- >>> ("hello","world") ^. both
-- "helloworld"
--
-- @
-- 'both' :: 'Traversal' (a , a) (b , b) a b
-- 'both' :: 'Traversal' (a + a) (b + b) a b
-- @
--
both :: Bitraversable f => Traversal (f a a) (f b b) a b
both = wander $ \f -> bitraverse f f
{-# INLINE both #-}

---------------------------------------------------------------------
-- 'TraversalRep'
---------------------------------------------------------------------

-- https://twanvl.nl/blog/haskell/non-regular1
data FList a b t = Done t | More a (FList a b (b -> t))

instance Functor (FList a b) where
  fmap f (Done t) = Done (f t)
  fmap f (More x l) = More x (fmap (f .) l)

instance Applicative (FList a b) where
  pure = Done
  Done f <*> fa = fmap f fa
  More x l <*> l' = More x (fmap flip l <*> l')

instance (a ~ b) => Comonad (FList a b) where
  extract (Done a) = a
  extract (More s r) = extract r s
  extend f (Done a) = Done (f (Done a))
  extend f (More s r) = More s (extend (\r' s' -> f (More s' r')) r)

single :: a -> FList a b b
single x = More x (Done id)

fuse :: FList b b t -> t
fuse (Done t) = t
fuse (More x l) = fuse l x

wander :: ((x -> FList x y y) -> s -> FList a b t) -> TraversalLike p s t a b
wander f = dimap (f single) fuse . prim_traversal

prim_traversal :: Choice p => PSemigroup (,) p => p a b -> p (FList a c t) (FList b c t)
prim_traversal k = dimap uncons cons (right' (k *** (prim_traversal k)))
  where
    uncons :: FList a b t -> t + (a, FList a b (b -> t))
    uncons (Done t) = Left t
    uncons (More x l) = Right (x, l)

    cons :: t + (a, FList a b (b -> t)) -> FList a b t
    cons (Left t) = Done t
    cons (Right (x, l)) = More x l

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
-- traverseOf $ _1 . _R :: Applicative f => (a -> f b) -> (c1 + a, c2) -> f (c1 + b, c2)
-- traverseOf == between runStar Star 
-- @

-- | TODO: Document
--
traverseOf :: Applicative f => ATraversal f s t a b -> (a -> f b) -> s -> f t
traverseOf o f = tf where Star tf = o (Star f)

-- | TODO: Document
--
sequenceOf :: Applicative f => ATraversal f s t (f a) a -> s -> f t
sequenceOf t = traverseOf t id

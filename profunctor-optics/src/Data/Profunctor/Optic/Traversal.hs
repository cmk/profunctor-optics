module Data.Profunctor.Optic.Traversal where

import Control.Applicative.Free.Fast
import Data.Bitraversable
import Data.Foldable (traverse_)
import Data.Functor.Identity
import Data.Profunctor.Choice
import Data.Profunctor.Monad
import Data.Profunctor.Optic.Prelude
import Data.Profunctor.Optic.Type
import Data.Profunctor.Strong
import Data.Profunctor.Types
import Data.Profunctor.Unsafe
import Data.Traversable (fmapDefault, foldMapDefault)
import Prelude hiding (mapM, id, (.))

import qualified Control.Arrow as A
import qualified Control.Category as C
import qualified Data.Tuple as T

import qualified Data.Profunctor.Traversing as T

---------------------------------------------------------------------
-- 'Traversal'
---------------------------------------------------------------------

-- | TODO: Document, DList
--
traversal :: Traversable f => (s -> f a) -> (s -> f b -> t) -> Traversal s t a b
traversal sa sbt = dimap dup (uncurry sbt) . psecond . lmap sa . lift traverse

-- | TODO: Document
--
traversed :: Traversable f => Traversal (f a) (f b) a b
traversed = lift traverse

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
both = lift $ \f -> bitraverse f f
{-# INLINE both #-}

vltraversal :: (forall f. Applicative f => (a -> f b) -> s -> f t) -> Traversal s t a b
vltraversal = lift

---------------------------------------------------------------------
-- 'TraversalRep'
---------------------------------------------------------------------

newtype TraversalRep p a b s t = TraversalRep (forall f. Applicative f => p a (f b) -> s -> f t)

runTraversalRep :: forall p a b s t. TraversalRep p a b s t -> (forall f. Applicative f => p a (f b) -> s -> f t)
runTraversalRep (TraversalRep x) = x

instance Profunctor (TraversalRep p a b) where
  dimap f g (TraversalRep b) = TraversalRep $ \pafb s -> g <$> b pafb (f s)

instance Strong (TraversalRep p a b) where
  first' (TraversalRep b) = TraversalRep (\pafb (x, y) -> flip (,) y <$> b pafb x)
  second' (TraversalRep b) = TraversalRep (\pafb (x, y) -> (x,) <$> b pafb y)

instance Choice (TraversalRep p a b) where
  left' (TraversalRep b) = TraversalRep (\pafb e -> bitraverse (b pafb) pure e)
  right' (TraversalRep b) = TraversalRep (\pafb e -> traverse (b pafb) e)

instance T.Traversing (TraversalRep p a b) where
  wander w (TraversalRep f) = TraversalRep (\pafb s -> w (f pafb) s)

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

wander'' :: (forall x. Applicative (p x)) => ((x -> FList x y y) -> s -> FList a b t) -> TraversalLike p s t a b
wander'' f = dimap (f single) fuse . prim_traversal

wander' :: (forall f. Applicative f => (a -> f b) -> s -> f t) -> Optic (TraversalRep p a b) s t a b
wander' w (TraversalRep f) = TraversalRep (\pafb s -> w (f pafb) s)

prim_traversal :: Choice p => (forall x. Applicative (p x)) => p a b -> p (FList a c t) (FList b c t)
prim_traversal k = dimap uncons cons (pright (k @@@ (prim_traversal k)))
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

-- | TODO: Document
--
-- ^ @
-- traverseOf :: Functor f => Lens s t a b -> (a -> f b) -> s -> f t
-- traverseOf :: Applicative f => Traversal s t a b -> (a -> f b) -> s -> f t
-- traverseOf $ _1 . _R :: Applicative f => (a -> f b) -> (c + a, d) -> f (c + b, d)
-- traverseOf == between runStar Star
-- @
--
traverseOf :: Applicative f => ATraversal f s t a b -> (a -> f b) -> s -> f t
traverseOf = between runStar Star

-- | TODO: Document
--
sequenceOf :: Applicative f => ATraversal f s t (f a) a -> s -> f t
sequenceOf t = traverseOf t id

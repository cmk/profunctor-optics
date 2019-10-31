module Data.Profunctor.Optic.Traversal where

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

traversalVL :: (forall f. Applicative f => (a -> f b) -> s -> f t) -> Traversal s t a b
traversalVL = lift

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

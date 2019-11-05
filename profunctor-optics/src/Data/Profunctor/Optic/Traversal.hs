module Data.Profunctor.Optic.Traversal where

import Data.Bitraversable
import Data.Profunctor.Optic.Prelude
import Data.Profunctor.Optic.Type

---------------------------------------------------------------------
-- 'Traversal'
---------------------------------------------------------------------

-- | TODO: Document
--
traversal :: Traversable f => (s -> f a) -> (s -> f b -> t) -> Traversal s t a b
traversal sa sbt = dimap dup (uncurry sbt) . psecond . lmap sa . lift traverse

-- | Transform a Van Laarhoven 'Traversal' into a profunctor 'Traversal'.
--
-- /Caution/: In order for the generated family to be well-defined,
-- you must ensure that the traversal laws hold for the input function:
--
-- * @abst pure ≡ pure@
--
-- * @fmap (abst f) . abst g ≡ getCompose . abst (Compose . fmap f . g)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
traversalVL :: (forall f. Applicative f => (a -> f b) -> s -> f t) -> Traversal s t a b
traversalVL abst = lift abst

-- | TODO: Document
--
traversed :: Traversable f => Traversal (f a) (f b) a b
traversed = lift traverse

---------------------------------------------------------------------
-- Primitive Operators
---------------------------------------------------------------------

-- | The traversal laws can be stated in terms or 'traverseOf' as well.
-- 
-- Identity:
-- 
-- @
-- traverseOf t (Identity . f) ≡  Identity (fmap f)
-- @
-- 
-- Composition:
-- 
-- @ 
-- Compose . fmap (traverseOf t f) . traverseOf t g ≡ traverseOf t (Compose . fmap f . g)
-- @
--
-- @
-- traverseOf :: Functor f => Lens s t a b -> (a -> f b) -> s -> f t
-- traverseOf :: Applicative f => Traversal s t a b -> (a -> f b) -> s -> f t
-- @
--
traverseOf :: Applicative f => ATraversal f s t a b -> (a -> f b) -> s -> f t
traverseOf = between runStar Star

-- | TODO: Document
--
sequenceOf :: Applicative f => ATraversal f s t (f a) a -> s -> f t
sequenceOf t = traverseOf t id

---------------------------------------------------------------------
-- Common 'Traversal's
---------------------------------------------------------------------

-- | Traverse bitraversed parts of a 'Bitraversable' container with matching types.
--
-- >>> traverseOf bitraversed (pure . length) (Right "hello")
-- Right 5
--
-- >>> traverseOf bitraversed (pure . length) ("hello","world")
-- (5,5)
--
-- >>> ("hello","world") ^. bitraversed
-- "helloworld"
--
-- @
-- 'bitraversed' :: 'Traversal' (a , a) (b , b) a b
-- 'bitraversed' :: 'Traversal' (a + a) (b + b) a b
-- @
--
bitraversed :: Bitraversable f => Traversal (f a a) (f b b) a b
bitraversed = lift $ \f -> bitraverse f f
{-# INLINE bitraversed #-}

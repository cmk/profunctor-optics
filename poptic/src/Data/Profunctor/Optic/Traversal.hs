{-# LANGUAGE GADTs #-}
module Data.Profunctor.Optic.Traversal (
    module Data.Profunctor.Optic.Traversal 
  , module Export
) where

import Data.Bitraversable 
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Operator
import Data.Profunctor.Optic.Prelude

import Data.Profunctor.Optic.Traversal.Affine    as Export
import Data.Profunctor.Optic.Traversal.NonEmpty  as Export
import Data.Profunctor.Traversing                as Export

import Data.Traversable (fmapDefault, foldMapDefault)


import Control.Applicative.Free (Ap, liftAp, runAp)
import Data.Functor.Identity

-- Free applicative over Identity if you could force Identity to be monomorphic on x.
data Mono x y a where
  Mono :: x -> Mono x y y

liftMono :: x -> Ap (Mono x y) y
liftMono = liftAp . Mono

unMono :: (x -> y) -> Mono x y a -> a
unMono f (Mono x) = f x

runMono :: (x -> y) -> Ap (Mono x y) a -> a
runMono f = runIdentity . runAp (Identity . unMono f)

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

sequenceOf :: Applicative f => Traversal s t (f a) a -> s -> f t
sequenceOf t = traverseOf t id

data FunList a b t = Done t | More a (FunList a b (b -> t))

traversalVL :: (forall f. Applicative f => (a -> f b) -> ta -> f tb) -> Traversal ta tb a b
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

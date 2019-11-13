module Data.Profunctor.Arrow.Traversing (
    FreeTraversing(..)
  , TraversingA
  , liftTraversing
  , foldTraversing
  , foldTraversing'
  , runTraversingT
  , runTraversingM
  , runTraversingM'
) where

import Control.Arrow (Kleisli(..))
import Control.Category hiding ((.), id)
import Data.Functor.Identity
import Data.Profunctor.Arrow
import Data.Profunctor.Arrow.Free 
import Data.Profunctor.Traversing
import Data.Profunctor

import Prelude

type TraversingA p = Free (FreeTraversing p)

{-# INLINE liftTraversing #-}
-- | TODO: Document
--
liftTraversing :: p a b -> TraversingA p a b
liftTraversing p = Free (FreeTraversing runIdentity p Identity) (Parr id)

-- | TODO: Document
--
foldTraversing :: Category q => Profunctor q => (forall f x y . Traversable f => p x y -> q (f x) (f y)) -> TraversingA p a b -> q a b
foldTraversing _ (Parr ab) = arr ab
foldTraversing pq (Free (FreeTraversing r p l) f) = dimap l r (pq p) <<< foldTraversing pq f

{-# INLINE foldTraversing' #-}
-- | TODO: Document
--
foldTraversing' :: Category q => Traversing q => p :-> q -> TraversingA p a b -> q a b
foldTraversing' pq = foldFree (runTraversingT pq)

{-# INLINE runTraversingT #-}
-- | TODO: Document
--
runTraversingT :: Traversing q => p :-> q -> FreeTraversing p a b -> q a b
runTraversingT pq (FreeTraversing r p l) = dimap l r (traverse' (pq p))


{-# INLINE runTraversingM #-}
-- | TODO: Document
--
runTraversingM :: Monad m => (forall f x y . Traversable f => p x y -> f x -> m (f y)) -> TraversingA p a b -> a -> m b 
runTraversingM f = runKleisli . foldTraversing (Kleisli . f)

{-# INLINE runTraversingM' #-}
-- | TODO: Document
--
runTraversingM' :: Monad m => (forall x y. p x y -> x -> m y) -> TraversingA p a b -> a -> m b
runTraversingM' f = runKleisli . foldTraversing' (Kleisli . f)

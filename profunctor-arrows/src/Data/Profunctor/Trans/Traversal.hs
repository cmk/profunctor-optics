module Data.Profunctor.Trans.Traversal (
    TraversalT
  , FreeTraversal
  , liftTraversal
  , foldTraversal
  , foldTraversing
  , runTraversalT
  , runTraversalM
  , runTraversingM
) where

import Control.Arrow (Arrow, Kleisli(..))
import Control.Category hiding ((.), id)
import Control.Comonad (Comonad, Cokleisli(..))

import Data.Profunctor.Arrow
import Data.Profunctor.Arrow.Free 
import Data.Profunctor.Traversing
import Data.Profunctor.Trans.Internal
import Data.Profunctor
import Data.Profunctor.Extra
import Data.Profunctor.Composition

import Prelude

type FreeTraversal p = Free (TraversalT p)

{-# INLINE liftTraversal #-}
-- | TODO: Document
--
liftTraversal :: p a b -> FreeTraversal p a b
liftTraversal p = Free (traversal_lift p) (Parr id)

-- | TODO: Document
--
foldTraversal :: Category q => Profunctor q => (forall f x y . Traversable f => p x y -> q (f x) (f y)) -> FreeTraversal p a b -> q a b
foldTraversal _ (Parr ab) = arr ab
foldTraversal pq (Free (Trans l p r) f) = dimap l r (pq p) <<< foldTraversal pq f

{-# INLINE foldTraversing #-}
-- | TODO: Document
--
foldTraversing :: Category q => Traversing q => p :-> q -> FreeTraversal p a b -> q a b
foldTraversing pq = foldFree (runTraversalT pq)

{-# INLINE runTraversalT #-}
-- | TODO: Document
--
runTraversalT :: Traversing q => p :-> q -> TraversalT p a b -> q a b
runTraversalT pq (Trans l p r) = dimap l r (traverse' (pq p))


{-# INLINE runTraversalM #-}
-- | TODO: Document
--
runTraversalM :: Monad m => (forall f x y . Traversable f => p x y -> f x -> m (f y)) -> FreeTraversal p a b -> a -> m b 
runTraversalM f = runKleisli . foldTraversal (Kleisli . f)

{-# INLINE runTraversingM #-}
-- | TODO: Document
--
runTraversingM :: Monad m => (forall x y. p x y -> x -> m y) -> FreeTraversal p a b -> a -> m b
runTraversingM f = runKleisli . foldTraversing (Kleisli . f)

{-
liftTraversing :: p a b -> Free (FreeTraversing p) a b
liftTraversing = Free (FreeTraversing runIdentity f Identity) (Parr id)
-}

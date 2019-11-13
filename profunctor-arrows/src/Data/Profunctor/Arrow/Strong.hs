module Data.Profunctor.Arrow.Strong (
    Pastro(..)
  , StrongA
  , liftStrong
  , foldStrong
  , runStrongT
  , runStrongM
) where

import Control.Arrow (Kleisli(..))
import Control.Category hiding ((.), id)
import Data.Profunctor
import Data.Profunctor.Arrow.Free 
import Data.Profunctor.Extra
import Data.Profunctor.Strong

import Prelude

type StrongA p = Free (Pastro p)

{-# INLINE liftStrong #-}
-- | TODO: Document
--
liftStrong :: p a b -> StrongA p a b
liftStrong p = Free (Pastro fst p fork) (Parr id)

{-# INLINE foldStrong #-}
-- | TODO: Document
--
foldStrong :: Category q => Strong q => p :-> q -> StrongA p a b -> q a b
foldStrong pq = foldFree (runStrongT pq)

{-# INLINE runStrongT #-}
-- | TODO: Document
--
runStrongT :: Strong q => p :-> q -> Pastro p a b -> q a b
runStrongT pq (Pastro r p l) = dimap l r (first' (pq p))

{-# INLINE runStrongM #-}
-- | TODO: Document
--
runStrongM :: Monad m => (forall x y. p x y -> x -> m y) -> StrongA p a b -> a -> m b
runStrongM f = runKleisli . foldStrong (Kleisli . f)

module Data.Profunctor.Trans.Strong (
    StrongT
  , FreeStrong
  , liftStrong
  , foldStrong
  , runStrongT
  , runStrongM
) where

import Control.Arrow (Arrow, Kleisli(..))
import Control.Category hiding ((.), id)
import Control.Comonad (Comonad, Cokleisli(..))
import Data.Profunctor
import Data.Profunctor.Arrow
import Data.Profunctor.Arrow.Free 
import Data.Profunctor.Composition
import Data.Profunctor.Extra
import Data.Profunctor.Strong
import Data.Profunctor.Trans.Internal

import Prelude

type FreeStrong p = Free (StrongT p)

{-# INLINE liftStrong #-}
-- | TODO: Document
--
liftStrong :: p a b -> FreeStrong p a b
liftStrong p = Free (strong_lift p) (Parr id)

{-# INLINE foldStrong #-}
-- | TODO: Document
--
foldStrong :: Category q => Strong q => p :-> q -> FreeStrong p a b -> q a b
foldStrong pq = foldFree (runStrongT pq)

{-# INLINE runStrongT #-}
-- | TODO: Document
--
runStrongT :: Strong q => p :-> q -> StrongT p a b -> q a b
runStrongT pq (Trans l p r) = dimap l r (second' (pq p))

{-# INLINE runStrongM #-}
-- | TODO: Document
--
runStrongM :: Monad m => (forall x y. p x y -> x -> m y) -> FreeStrong p a b -> a -> m b
runStrongM f = runKleisli . foldStrong (Kleisli . f)


{- delete?
type FreePastro p = Free (Pastro p)

liftPastro :: p a b -> FreePastro p a b
liftPastro p = Free (Pastro fst p fork) (Parr id)

-}

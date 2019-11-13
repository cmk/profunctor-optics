module Data.Profunctor.Arrow.Adapter (
    Coyoneda
  , AdapterA
  , liftAdapter
  , foldAdapter
  , runAdapterT
  , runAdapterM
  , runAdapterW
) where

import Control.Arrow (Kleisli(..))
import Control.Category hiding ((.), id)
import Control.Comonad (Comonad, Cokleisli(..))
import Data.Profunctor
import Data.Profunctor.Arrow.Free 
import Data.Profunctor.Yoneda

import Prelude

type AdapterA p = Free (Coyoneda p)

{-# INLINE liftAdapter #-}
-- | TODO: Document
--
liftAdapter :: p a b -> AdapterA p a b
liftAdapter p = Free (Coyoneda id id p) (Parr id)

{-# INLINE foldAdapter #-}
-- | TODO: Document
--
foldAdapter :: Category q => Profunctor q => p :-> q -> AdapterA p a b -> q a b
foldAdapter pq = foldFree (runAdapterT pq)

{-# INLINE runAdapterT #-}
-- | TODO: Document
--
runAdapterT :: Profunctor q => p :-> q -> Coyoneda p a b -> q a b
runAdapterT pq (Coyoneda l r p) = dimap l r (pq p)

{-# INLINE runAdapterM #-}
-- | TODO: Document
--
runAdapterM :: Monad m => (forall x y. p x y -> x -> m y) -> AdapterA p a b -> a -> m b
runAdapterM f = runKleisli . foldAdapter (Kleisli . f)

{-# INLINE runAdapterW #-}
-- | TODO: Document
--
runAdapterW :: Comonad w => (forall x y. p x y -> w x -> y) -> AdapterA p a b -> w a -> b
runAdapterW f = runCokleisli . foldAdapter (Cokleisli . f)

module Data.Profunctor.Trans.Adapter (
    Coyoneda
  , FreeAdapter
  , liftAdapter
  , foldAdapter
  , runAdapterT
  , runAdapterM
  , runAdapterW
) where

import Control.Arrow (Arrow, Kleisli(..))
import Control.Category hiding ((.), id)
import Control.Comonad (Comonad, Cokleisli(..))
import Data.Profunctor
import Data.Profunctor.Arrow
import Data.Profunctor.Arrow.Free 
import Data.Profunctor.Composition
import Data.Profunctor.Extra
import Data.Profunctor.Trans.Internal
import Data.Profunctor.Yoneda

import Prelude

type FreeAdapter p = Free (Coyoneda p)

{-# INLINE liftAdapter #-}
-- | TODO: Document
--
liftAdapter :: p a b -> FreeAdapter p a b
liftAdapter p = Free (Coyoneda id id p) (Parr id)

{-# INLINE foldAdapter #-}
-- | TODO: Document
--
foldAdapter :: Category q => Profunctor q => p :-> q -> FreeAdapter p a b -> q a b
foldAdapter pq = foldFree (runAdapterT pq)

{-# INLINE runAdapterT #-}
-- | TODO: Document
--
runAdapterT :: Profunctor q => p :-> q -> Coyoneda p a b -> q a b
runAdapterT pq (Coyoneda l r p) = dimap l r (pq p)

{-# INLINE runAdapterM #-}
-- | TODO: Document
--
runAdapterM :: Monad m => (forall x y. p x y -> x -> m y) -> FreeAdapter p a b -> a -> m b
runAdapterM f = runKleisli . foldAdapter (Kleisli . f)

{-# INLINE runAdapterW #-}
-- | TODO: Document
--
runAdapterW :: Comonad w => (forall x y. p x y -> w x -> y) -> FreeAdapter p a b -> w a -> b
runAdapterW f = runCokleisli . foldAdapter (Cokleisli . f)

{- delete?
type FreePastroSum p = Free (PastroSum p)

foldPastroSum :: Category q => Adapter q => p :-> q -> FreePastroSum p a b -> q a b
foldPastroSum pq = foldFree (runPastroSum pq)

runPastroSum :: Profunctor q => p :-> q -> PastroSum p a b -> q a b
runPastroSum pq (PastroSum r p l) = dimap l r (left' (pq p))

runPastroSumM :: Monad m => (forall x y. p x y -> x -> m y) -> FreePastroSum p a b -> (a -> m b)
runPastroSumM f = runKleisli . foldPastroSum (Kleisli . f)

runPastroSumW :: Comonad w => (forall x y. p x y -> w x -> y) -> FreePastroSum p a b -> (w a -> b)
runPastroSumW f = runCokleisli . foldPastroSum (Cokleisli . f)
-}

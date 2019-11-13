module Data.Profunctor.Trans.Choice (
    ChoiceT
  , FreeChoice
  , liftChoice
  , foldChoice
  , runChoiceT
  , runChoiceM
  , runChoiceW
) where

import Control.Arrow (Arrow, Kleisli(..))
import Control.Category hiding ((.), id)
import Control.Comonad (Comonad, Cokleisli(..))

import Data.Profunctor.Arrow
import Data.Profunctor.Arrow.Free 
import Data.Profunctor.Choice
import Data.Profunctor.Trans.Internal
import Data.Profunctor
import Data.Profunctor.Extra
import Data.Profunctor.Composition

import Prelude

type FreeChoice p = Free (ChoiceT p)

{-# INLINE liftChoice #-}
-- | TODO: Document
--
liftChoice :: p a b -> FreeChoice p a b
liftChoice p = Free (choice_lift p) (Parr id)

{-# INLINE foldChoice #-}
-- | TODO: Document
--
foldChoice :: Category q => Choice q => p :-> q -> FreeChoice p a b -> q a b
foldChoice pq = foldFree (runChoiceT pq)

{-# INLINE runChoiceT #-}
-- | TODO: Document
--
runChoiceT :: Choice q => p :-> q -> ChoiceT p a b -> q a b
runChoiceT pq (Trans l p r) = dimap l r (right' (pq p))

{-# INLINE runChoiceM #-}
-- | TODO: Document
--
runChoiceM :: Monad m => (forall x y. p x y -> x -> m y) -> FreeChoice p a b -> (a -> m b)
runChoiceM f = runKleisli . foldChoice (Kleisli . f)

{-# INLINE runChoiceW #-}
-- | TODO: Document
--
runChoiceW :: Comonad w => (forall x y. p x y -> w x -> y) -> FreeChoice p a b -> (w a -> b)
runChoiceW f = runCokleisli . foldChoice (Cokleisli . f)

{- delete?
type FreePastroSum p = Free (PastroSum p)

foldPastroSum :: Category q => Choice q => p :-> q -> FreePastroSum p a b -> q a b
foldPastroSum pq = foldFree (runPastroSum pq)

runPastroSum :: Choice q => p :-> q -> PastroSum p a b -> q a b
runPastroSum pq (PastroSum r p l) = dimap l r (left' (pq p))

runPastroSumM :: Monad m => (forall x y. p x y -> x -> m y) -> FreePastroSum p a b -> (a -> m b)
runPastroSumM f = runKleisli . foldPastroSum (Kleisli . f)

runPastroSumW :: Comonad w => (forall x y. p x y -> w x -> y) -> FreePastroSum p a b -> (w a -> b)
runPastroSumW f = runCokleisli . foldPastroSum (Cokleisli . f)
-}

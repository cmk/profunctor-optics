module Data.Profunctor.Arrow.Choice (
    PastroSum(..)
  , ChoiceA
  , liftChoice
  , foldChoice
  , runChoiceT
  , runChoiceM
  , runChoiceW
) where

import Control.Arrow (Kleisli(..))
import Control.Category hiding ((.), id)
import Control.Comonad (Comonad, Cokleisli(..))

import Data.Profunctor.Arrow.Free 
import Data.Profunctor.Choice
import Data.Profunctor
import Data.Profunctor.Extra

import Prelude

type ChoiceA p = Free (PastroSum p)

{-# INLINE liftChoice #-}
-- | TODO: Document
--
liftChoice :: p a b -> ChoiceA p a b
liftChoice p = Free (PastroSum lft' p Left) (Parr id)

{-# INLINE foldChoice #-}
-- | TODO: Document
--
foldChoice :: Category q => Choice q => p :-> q -> ChoiceA p a b -> q a b
foldChoice pq = foldFree (runChoiceT pq)

{-# INLINE runChoiceT #-}
-- | TODO: Document
--
runChoiceT :: Choice q => p :-> q -> PastroSum p a b -> q a b
runChoiceT pq (PastroSum r p l) = dimap l r (left' (pq p))

{-# INLINE runChoiceM #-}
-- | TODO: Document
--
runChoiceM :: Monad m => (forall x y. p x y -> x -> m y) -> ChoiceA p a b -> (a -> m b)
runChoiceM f = runKleisli . foldChoice (Kleisli . f)

{-# INLINE runChoiceW #-}
-- | TODO: Document
--
runChoiceW :: Comonad w => (forall x y. p x y -> w x -> y) -> ChoiceA p a b -> (w a -> b)
runChoiceW f = runCokleisli . foldChoice (Cokleisli . f)

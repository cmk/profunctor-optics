module Data.Profunctor.Trans.Closed (
    ClosedT
  , FreeClosed
  , liftClosed
  , foldClosed
  , runClosedT
  , runClosedM
  , runClosedW
) where

import Control.Arrow (Arrow, Kleisli(..))
import Control.Category hiding ((.), id)
import Control.Comonad (Comonad, Cokleisli(..))
import Data.Distributive
import Data.Profunctor
import Data.Profunctor.Arrow
import Data.Profunctor.Arrow.Free 
import Data.Profunctor.Closed
import Data.Profunctor.Composition
import Data.Profunctor.Extra
import Data.Profunctor.Trans.Internal

import Prelude

type FreeClosed p = Free (ClosedT p)

{-# INLINE liftClosed #-}
-- | TODO: Document
--
liftClosed :: p a b -> FreeClosed p a b
liftClosed p = Free (closed_lift p) (Parr id)

{-# INLINE foldClosed #-}
-- | TODO: Document
--
foldClosed :: Category q => Closed q => p :-> q -> FreeClosed p a b -> q a b
foldClosed pq = foldFree (runClosedT pq)

{-# INLINE runClosedT #-}
-- | TODO: Document
--
runClosedT :: Closed q => p :-> q -> ClosedT p a b -> q a b
runClosedT pq (Trans l p r) = dimap l r (closed (pq p))

{-# INLINE runClosedM #-}
-- | TODO: Document
--
runClosedM :: Distributive m => Monad m => (forall x y. p x y -> x -> m y) -> FreeClosed p a b -> a -> m b
runClosedM f = runKleisli . foldClosed (Kleisli . f)

{-# INLINE runClosedW #-}
-- | TODO: Document
--
runClosedW :: Comonad w => (forall x y. p x y -> w x -> y) -> FreeClosed p a b -> w a -> b
runClosedW f = runCokleisli . foldClosed (Cokleisli . f)

{- delete?
liftEnv :: p a b -> Free (Environment p) a b
liftEnv p = Free (Environment ($ ()) p const) (Parr id)

-}

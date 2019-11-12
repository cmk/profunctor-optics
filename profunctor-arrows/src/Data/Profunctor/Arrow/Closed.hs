module Data.Profunctor.Arrow.Closed (
    Environment(..)
  , ClosedA
  , liftClosed
  , foldClosed
  , runClosedT
  , runClosedW
) where

import Control.Category hiding ((.), id)
import Control.Comonad (Comonad, Cokleisli(..))
import Data.Profunctor
import Data.Profunctor.Arrow.Free 
import Data.Profunctor.Closed

import Prelude

type ClosedA p = Free (Environment p)

{-# INLINE liftClosed #-}
-- | TODO: Document
--
liftClosed :: p a b -> ClosedA p a b
liftClosed p = Free (Environment ($ ()) p const) (Parr id)

{-# INLINE foldClosed #-}
-- | TODO: Document
--
foldClosed :: Category q => Closed q => p :-> q -> ClosedA p a b -> q a b
foldClosed pq = foldFree (runClosedT pq)

{-# INLINE runClosedT #-}
-- | TODO: Document
--
runClosedT :: Closed q => p :-> q -> Environment p a b -> q a b
runClosedT pq (Environment r p l) = dimap l r (closed (pq p))

{-# INLINE runClosedW #-}
-- | TODO: Document
--
runClosedW :: Comonad w => (forall x y. p x y -> w x -> y) -> ClosedA p a b -> w a -> b
runClosedW f = runCokleisli . foldClosed (Cokleisli . f)

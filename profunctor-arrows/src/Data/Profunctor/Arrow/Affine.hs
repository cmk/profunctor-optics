module Data.Profunctor.Arrow.Affine (
    AffineT
  , AffineA
  , liftAffine
  , foldAffine
  , runAffineT
  , runAffineM
) where

import Control.Arrow (Kleisli(..))
import Control.Category hiding ((.), id)
import Data.Profunctor
import Data.Profunctor.Arrow.Free 
import Data.Profunctor.Arrow.Internal

import Prelude

type AffineA p = Free (AffineT p)

{-# INLINE liftAffine #-}
-- | TODO: Document
--
liftAffine :: p a b -> AffineA p a b
liftAffine p = Free (affine_lift p) (Parr id)

{-# INLINE foldAffine #-}
-- | TODO: Document
--
foldAffine :: Category q => Choice q => Strong q => p :-> q -> AffineA p a b -> q a b
foldAffine pq = foldFree (runAffineT pq)

{-# INLINE runAffineT #-}
-- | TODO: Document
--
runAffineT :: Choice q => Strong q => p :-> q -> AffineT p a b -> q a b
runAffineT pq (Trans l p r) = dimap l r (affine (pq p))

{-# INLINE runAffineM #-}
-- | TODO: Document
--
runAffineM :: Monad m => (forall x y. p x y -> x -> m y) -> AffineA p a b -> a -> m b
runAffineM f = runKleisli . foldAffine (Kleisli . f)

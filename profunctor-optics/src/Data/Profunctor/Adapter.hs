module Data.Profunctor.Adapter where

import Data.Profunctor.Types
import Data.Functor.Identity

import Prelude 
--lowerStar :: Adapter Identity f a b -> Star f a b
newtype Adapter f g a b = Adapter { runAdapter :: g a -> f b }

--instance Functor f => Functor (Adapter f g a) where
--instance (Functor f, Functor g) => Profunctor (Adapter f g) where


lower' :: Adapter f g a c -> Star f (g a) c
lower' = Star . runAdapter 

lowerCostar :: Adapter Identity g d c -> Costar g d c
lowerCostar = Costar . (runIdentity .) . runAdapter

lowerStar :: Adapter f Identity d c -> Star f d c
lowerStar = Star . (. Identity) . runAdapter


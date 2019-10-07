module Data.Profunctor.Bistar where

import Data.Profunctor.Types
import Data.Functor.Identity

import Prelude 
--lowerStar :: Adapter Identity f a b -> Star f a b
newtype Bistar f g a b = Bistar { runBistar :: g a -> f b }

--instance Functor f => Functor (Bistar f g a) where
--instance (Functor f, Functor g) => Profunctor (Bistar f g) where


lower' :: Bistar f g a c -> Star f (g a) c
lower' = Star . runBistar 

lowerCostar :: Bistar Identity g d c -> Costar g d c
lowerCostar = Costar . (runIdentity .) . runBistar

lowerStar :: Bistar f Identity d c -> Star f d c
lowerStar = Star . (. Identity) . runBistar


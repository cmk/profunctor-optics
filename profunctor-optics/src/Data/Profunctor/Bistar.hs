module Data.Profunctor.Bistar where

import Data.Profunctor.Types
import Data.Functor.Identity
import Data.Functor.Foldable

import Control.Monad.Free (Free(..))
import Control.Comonad.Cofree (Cofree(..))

import Prelude

--lowerStar :: Bistar Identity f a b -> Star f a b
newtype Bistar f g a b = Bistar { runBistar :: g a -> f b }

--instance Functor f => Functor (Bistar f g a) where
--instance (Functor f, Functor g) => Profunctor (Bistar f g) where


lower' :: Bistar f g a c -> Star f (g a) c
lower' = Star . runBistar 

lowerCostar :: Bistar Identity g d c -> Costar g d c
lowerCostar = Costar . (runIdentity .) . runBistar

lowerStar :: Bistar f Identity d c -> Star f d c
lowerStar = Star . (. Identity) . runBistar

bicata :: Functor f => Bistar Identity f (Identity a) (f a)
bicata = Bistar distCata

biana :: Functor f => Bistar f Identity (f a) (Identity a)
biana = Bistar distAna

biapo :: Recursive t => Bistar (Base t) (Either t) (Base t a) (Either t a)
biapo = Bistar distApo

bipara :: Corecursive t => Bistar ((,) t) (Base t) (t, a) (Base t a)
bipara = Bistar distPara

bihisto :: Functor f => Bistar (Cofree f) f (Cofree f a) (f a)
bihisto = Bistar distHisto

bifutu :: Functor f => Bistar f (Free f) (f a) (Free f a)
bifutu = Bistar distFutu

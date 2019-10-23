module Data.Profunctor.Orphan where

import Control.Comonad
import Data.Functor.Contravariant
import Data.Profunctor
import Data.Profunctor.Choice
import Data.Profunctor.Closed

import Prelude

instance Cochoice (Forget r) where 
  unleft (Forget f) = Forget $ f . Left

  unright (Forget f) = Forget $ f . Right

instance Comonad f => Strong (Costar f) where
  first' (Costar f) = Costar $ \x -> (f (fmap fst x), snd (extract x))

  second' (Costar f) = Costar $ \x -> (fst (extract x), f (fmap snd x))

instance Contravariant f => Contravariant (Star f a) where
  contramap f (Star g) = Star $ contramap f . g

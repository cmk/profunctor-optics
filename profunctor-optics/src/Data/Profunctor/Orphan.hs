module Data.Profunctor.Orphan where

import Control.Applicative
import Control.Comonad
import Control.Foldl
import Data.Distributive
import Data.Foldable
import Data.Functor.Contravariant
import Data.Functor.Rep as Functor
import Data.Monoid
import Data.Profunctor
import Data.Profunctor.Choice
import Data.Profunctor.Closed
import Data.Profunctor.Rep as Profunctor
import Data.Profunctor.Sieve

import Prelude

instance Cochoice (Forget r) where 
  unleft (Forget f) = Forget $ f . Left

  unright (Forget f) = Forget $ f . Right

instance Comonad f => Strong (Costar f) where
  first' (Costar f) = Costar $ \x -> (f (fmap fst x), snd (extract x))

  second' (Costar f) = Costar $ \x -> (fst (extract x), f (fmap snd x))

instance Contravariant f => Contravariant (Star f a) where
  contramap f (Star g) = Star $ contramap f . g

instance Distributive (Fold a) where
  distribute = distributeRep
  {-# INLINE distribute #-}

instance Functor.Representable (Fold a) where
  type Rep (Fold a) = [a]
  index = cosieve
  tabulate = cotabulate

instance Costrong Fold where
  unfirst = unfirstCorep
  unsecond = unsecondCorep

instance Closed Fold where
  closed (Fold h z k) = Fold (liftA2 h) (pure z) (\f x -> k (f x))

-- | >>> cosieve (Fold (+) 0 id) [1,2,3]
-- 6
instance Cosieve Fold [] where
  cosieve (Fold h0 z0 k0) as0 = go k0 h0 z0 as0 where
    go k _ z [] = k z
    go k h z (a:as) = go k h (h z a) as
  {-# INLINE cosieve #-}

instance Corepresentable Fold where
  type Corep Fold = []
  cotabulate f = Fold (flip (:)) [] (f . reverse)
  {-# INLINE cotabulate #-}

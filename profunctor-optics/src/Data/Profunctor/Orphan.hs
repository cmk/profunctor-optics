{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Orphan where

import Control.Applicative
import Control.Comonad
import Control.Foldl
import Data.Distributive
import Data.Bifunctor
import Data.Functor.Apply
import Data.Functor.Contravariant
import Data.Profunctor
import Data.Profunctor.Rep as Profunctor
import Data.Profunctor.Sieve

import Prelude

instance Contravariant f => Contravariant (Star f a) where
  contramap f (Star g) = Star $ contramap f . g

instance Contravariant f => Bifunctor (Costar f) where
  first f (Costar g) = Costar $ g . contramap f

  second f (Costar g) = Costar $ f . g

instance Cochoice (Forget r) where 
  unleft (Forget f) = Forget $ f . Left

  unright (Forget f) = Forget $ f . Right

instance Comonad f => Strong (Costar f) where
  first' (Costar f) = Costar $ \x -> (f (fmap fst x), snd (extract x))

  second' (Costar f) = Costar $ \x -> (fst (extract x), f (fmap snd x))

run1 t (Fold h z k) = k (h z t)
prefix1 a = run1 a . duplicate

instance Distributive (Fold a) where
  distribute x = Fold (\fm a -> fmap (prefix1 a) fm) x (fmap extract)
  {-# INLINE distribute #-}

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

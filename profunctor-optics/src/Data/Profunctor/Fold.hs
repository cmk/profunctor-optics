{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies #-}
module Data.Profunctor.Fold (
    Fold(..)
  , module Data.Profunctor.Fold
  , module Export
  ) where

import Control.Applicative
import Control.Comonad
import Control.Monad.Reader.Class
import Control.Monad.Fix
import Control.Monad.Zip
import Data.Distributive
import Data.Foldable
import Data.Functor.Extend
import Data.Functor.Bind
import Data.Profunctor.Closed
import Data.Profunctor
import Data.Profunctor.Sieve
import Data.Profunctor.Rep as Profunctor
import Data.Profunctor.Unsafe
import Unsafe.Coerce
import Prelude hiding (foldl)

import Control.Foldl (Fold(..))
import qualified Control.Foldl as Export


run1 :: a -> Fold a p -> p
run1 t (Fold h z k) = k (h z t)

prefix1 :: a1 -> Fold a1 a2 -> Fold a1 a2
prefix1 x = run1 x . duplicate

moore :: (s -> (b, a -> s)) -> s -> Fold a b
moore f s = Fold (snd . f) s (fst . f)
{-# INLINE moore #-}

{-
mkFold :: (r -> b) -> (r -> a -> r) -> r -> Fold a b
mkFold k h z = Fold h z k

instance Scan mkFold where
  run1 t (L k h z)    = k (h z t)
  prefix1 a           = run1 a . duplicate
  postfix1 t a        = extend (run1 a) t
  interspersing a (L k h z) = mkFold (maybe' (k z) k) h' Nothing' where
    h' Nothing' b  = Just' (h z b)
    h' (Just' x) b = Just' (h (h x a) b)
  {-# INLINE run1 #-}
  {-# INLINE prefix1 #-}
  {-# INLINE postfix1 #-}
  {-# INLINE interspersing #-}

-- | efficient 'prefix', leaky 'postfix'
instance Folding Fold where
  run t (L k h z)     = k (foldl h z t)
  runOf l s (L k h z) = k (foldlOf l h z s)
  prefix s            = run s . duplicate
  prefixOf l s        = runOf l s . duplicate
  postfix t s         = extend (run s) t
  postfixOf l t s     = extend (runOf l s) t
  filtering p (L k h z) = mkFold k (\r a -> if p a then h r a else r) z
  {-# INLINE run #-}
  {-# INLINE runOf #-}
  {-# INLINE prefix #-}
  {-# INLINE prefixOf #-}
  {-# INLINE postfix #-}
  {-# INLINE postfixOf #-}
  {-# INLINE filtering #-}

-}

instance Apply (Fold a) where
  (<.>) = (<*>)
  {-# INLINE (<.>) #-}

  (<.) m = \_ -> m
  {-# INLINE (<.) #-}

  _ .> m = m
  {-# INLINE (.>) #-}

instance Distributive (Fold a) where
  distribute x = Fold (\fm a -> fmap (prefix1 a) fm) x (fmap extract)
  --distribute = distributeRep
  {-# INLINE distribute #-}

instance Costrong Fold where
  unfirst = unfirstCorep
  unsecond = unsecondCorep

-- | >>> cosieve (Fold (+) 0 id) [1,2,3]
-- 6

instance Cosieve Fold [] where
  cosieve (Fold h0 z0 k0) as0 = go k0 h0 z0 as0 where
    go k _ z [] = k z
    go k h z (a:as) = go k h (h z a) as
  {-# INLINE cosieve #-}

instance Closed Fold where
  closed (Fold h z k) = Fold (liftA2 h) (pure z) (\f x -> k (f x))

instance Corepresentable Fold where
  type Corep Fold = []
  cotabulate f = Fold (flip (:)) [] (f . reverse)
  {-# INLINE cotabulate #-}

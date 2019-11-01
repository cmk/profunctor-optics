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
import Data.Distributive
import Data.Foldable
import Data.Functor.Bind
import Data.Functor.Rep as Functor
import Data.Profunctor.Closed
import Data.Profunctor
import Data.Profunctor.Sieve
import Data.Profunctor.Rep as Profunctor
import Prelude hiding (foldl)
import Control.Foldl (Fold(..))
import qualified Data.Strict as S
import qualified Control.Foldl as Export

moore :: (s -> (b, a -> s)) -> s -> Fold a b
moore f s = Fold (snd . f) s (fst . f)
{-# INLINE moore #-}

run :: Foldable t => t a -> Fold a p -> p
run t (Fold h z k) = k $! foldl h z t
{-# INLINE run #-}

prefix :: Foldable t => t a1 -> Fold a1 a2 -> Fold a1 a2
prefix s = run s . duplicate
{-# INLINE prefix #-}

--leaky
postfix :: Foldable t => Fold a b -> t a -> Fold a b
postfix t s = extend (run s) t
{-# INLINE postfix #-}

run1 :: a -> Fold a p -> p
run1 t (Fold h z k) = k $! h z t
{-# INLINE run1 #-}

prefix1 :: a1 -> Fold a1 a2 -> Fold a1 a2
prefix1 x = run1 x . duplicate
{-# INLINE prefix1 #-}

postfix1 :: Fold a b -> a -> Fold a b
postfix1 t a = extend (run1 a) t
{-# INLINE postfix1 #-}

intersperse :: a -> Fold a b -> Fold a b
intersperse a (Fold h z k) = Fold h' S.Nothing (S.maybe (k z) k) where
  h' S.Nothing b  = S.Just (h z b)
  h' (S.Just x) b = S.Just (h (h x a) b)
{-# INLINE intersperse #-}

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

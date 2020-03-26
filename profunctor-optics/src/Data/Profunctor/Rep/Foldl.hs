
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE Safe                      #-}
{-# OPTIONS_GHC -fno-warn-orphans      #-}

module Data.Profunctor.Rep.Foldl (
  -- * Foldl
    type L
  , type Foldl
  , type IndexedFoldl
  , Fold (..)
  , withFoldl
  , run
  , foldl
  --, ifoldl
  , prefix
  , scan
  , prescan
  , postscan
  -- * Folds
  , mconcat
  , foldMap


  , head
  , last
  , lastDef
  --, lastN
  , null
  , length
  , and
  , or
  , all
  , any
  --, sum
  --, product
  --, mean
  --, variance
  --, std
  , maximum
  , maximumBy
  , minimum
  , minimumBy
  , elem
  , notElem
  , find
  , Control.Foldl.index
  , lookup
  , elemIndex
  , findIndex

  -- * Generic Folds
  , genericLength
  , genericIndex

  -- * Container folds
  , list
  , revList
  , nub
  , eqNub
  , set
  --, hashSet
  , map
  --, hashMap
  --, vector

  -- * Utilities
  -- $utilities
  , purely
  , purely_
  , _Fold1
  , premap
  , prefilter
  -- , predropWhile
  --, drop
  , Handler
  , handles
  , foldOver
  , folded
  , filtered
  , groupBy
  , either
  --, nest

  -- * EndoM
  , EndoM(..)
) where

import Control.Foldl hiding (product, sum)

import Control.Applicative
import Control.Monad.Fix (MonadFix(..))
import Control.Monad.Reader (MonadReader(..))
import Data.Distributive (Distributive (..))
--import Data.Key hiding (lookup)
import Data.Functor.Rep as Functor (Representable (..), askRep, localRep, mfixRep)
import Data.Profunctor (Costrong (..))
import Data.Profunctor.Closed (Closed (..))
import Data.Profunctor.Rep as Profunctor (Corepresentable (..), unfirstCorep, unsecondCorep)
import Data.Profunctor.Sieve (Cosieve (..))
--import Data.Semiring (type (-), Semiring, zero, one, (+), (*))

import Prelude as P hiding
  ( head, last, null, length, and, or, all, any, sum, product, maximum, 
    minimum, mconcat, elem, notElem, lookup, map, either, drop, 
    Num(..), Fractional(..), foldMap, foldl
  )

type L r a b = forall x. (x -> a -> x) -> x -> (x -> b) -> r

type Foldl = Fold

type IndexedFoldl i a b = Foldl (i, a) b

---------------------------------------------------------------------
-- Fold
---------------------------------------------------------------------

--data Fold a b = forall x. Fold (x -> a -> x) x (x -> b)

run :: Fold a b -> a -> b
run (Fold h z k) t = k (h z t)

prefix :: a -> Fold a b -> Fold a b
prefix a = flip run a . duplicate

-- | TODO: Document
--
withFoldl :: Fold a b -> L r a b -> r
withFoldl (Fold h z k) f = f h z k
{-# INLINE withFoldl #-}

foldl :: Foldable f => Foldl a b -> f a -> b
foldl = fold


{-
ifoldl :: FoldableWithKey f => IndexedFoldl (Key f) a b -> f a -> b
ifoldl (Fold step begin done) as = foldrWithKey cons done as begin
  where
    cons i a k x = k $! step x (i, a)

---------------------------------------------------------------------
-- Folds
---------------------------------------------------------------------

-- | Return the sum of all elements.
--
sum :: (Sum-Monoid) a => Fold a a
sum = sumWith id
{-# INLINABLE sum #-}

-- | Return the sum of all elements.
--
sumWith :: (Sum-Monoid) b => (a -> b) -> Fold a b
sumWith f = Fold (\x y -> x + f y) zero id
{-# INLINABLE sumWith #-}

-- | Return the product of all elements.
--
product :: (Product-Monoid) a => Fold a a
product = productWith id
{-# INLINABLE product #-}

-- | Return the product of all elements.
--
productWith :: (Product-Monoid) b => (a -> b) -> Fold a b
productWith f = Fold (\x y -> x * f y) one id
{-# INLINABLE productWith #-}

-- | Return the maximum element of a collection.
--
-- Returns /Nothing/ if the container is empty.
--
maximumMay :: Ord a => Fold a (Maybe a)
maximumMay = _Fold1 max
{-# INLINABLE maximumMay #-}

-- | Return the maximum element of a collection.
--
-- Returns a default value if the container is empty.
--
maximumDef :: Ord a => a -> Fold a a
maximumDef a = fmap (maybe a id) maximumMay
{-# INLINABLE maximumDef #-}

-- | Return the minimum element of a collection.
--
-- Returns /Nothing/ if the container is empty.
--
minimumMay :: Ord a => Fold a (Maybe a)
minimumMay = _Fold1 min
{-# INLINABLE minimumMay #-}

-- | Return the minimum element of a collection.
--
-- Returns a default value if the container is empty.
--
minimumDef :: Ord a => a -> Fold a a
minimumDef a = fmap (maybe a id) minimumMay
{-# INLINABLE minimumDef #-}
-}

---------------------------------------------------------------------
-- Orphan Fold instances
---------------------------------------------------------------------

-- Comonad instances

extract :: Fold a b -> b
extract (Fold _ z k) = k z

duplicate :: Fold a b -> Fold a (Fold a b)
duplicate (Fold h z k) = Fold h z (flip (Fold h) k)

--extend :: (Fold a b -> c) -> Fold a b -> Fold a c
--extend f (Fold h z k) = Fold h z (f . flip (Fold h) k)

instance Distributive (Fold a) where

  distribute z = Fold (\fm a -> fmap (prefix a) fm) z (fmap extract)

instance Functor.Representable (Fold a) where

  type Rep (Fold a) = [a]

  index = cosieve

  tabulate = cotabulate

instance Cosieve Fold [] where

  cosieve (Fold k0 h0 z0) as0 = go k0 h0 z0 as0
    where
      go _ z k [] = k z
      go h z k (a : as) = go h (h z a) k as

instance Closed Fold where

  closed (Fold h z k) = Fold (liftA2 h) (pure z) (\f x -> k (f x))

instance Costrong Fold where

  unfirst = unfirstCorep

  unsecond = unsecondCorep

instance Corepresentable Fold where

  type Corep Fold = []

  cotabulate f = Fold (flip (:)) [] (f . reverse)

instance Monad (Fold a) where

  m >>= f = Fold (flip (:)) [] (\xs -> flip fold xs . f) <*> m

instance MonadReader [a] (Fold a) where

  ask = askRep

  local = localRep

instance MonadFix (Fold a) where
  mfix = mfixRep


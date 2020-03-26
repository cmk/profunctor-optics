
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE RankNTypes                #-}
{-# OPTIONS_GHC -fno-warn-orphans      #-}

module Data.Profunctor.Rep.Foldl (
    type L
  -- * Foldl
  , Foldl (..)
  , run
  , foldl
  , withFoldl
  , prefix
  , prescan
  , postscan
  -- * Folds
  , list
  , revList
  , mconcat
  , stepMay
  , stepDef
  , headDef
  , lastDef
  , maximumDef
  , maximumByDef
  , minimumDef
  , minimumByDef
  ) where

import Control.Applicative
import Control.Monad.Fix (MonadFix(..))
import Control.Monad.Reader (MonadReader(..))
import Data.Distributive (Distributive (..))
import Data.Functor.Rep as Functor (Representable (..), askRep, localRep, mfixRep)
import Data.List (mapAccumL)
import Data.Profunctor
import Data.Profunctor.Closed (Closed (..))
import Data.Profunctor.Rep as Profunctor (Corepresentable (..), unfirstCorep, unsecondCorep)
import Data.Profunctor.Sieve (Cosieve (..))
import Data.Strict.Tuple
import Prelude as P hiding
  ( head, last, null, length, and, or, all, any, sum, product, maximum, 
    minimum, mconcat, elem, notElem, lookup, map, either, drop, 
    Num(..), Fractional(..), foldl
  )
import qualified Data.Foldable as F
import qualified Data.Strict.Maybe as M'

type L r a b = forall x. (x -> a -> x) -> x -> (x -> b) -> r

---------------------------------------------------------------------
-- Foldl
---------------------------------------------------------------------

data Foldl a b = forall x. Foldl (x -> a -> x) x (x -> b)

run :: Foldl a b -> a -> b
run (Foldl h z k) t = k (h z t)
{-# INLINABLE run #-}

foldl :: Foldable f => Foldl a b -> f a -> b
foldl (Foldl step begin done) as = F.foldr cons done as begin
  where
    cons a k x = k $! step x a
{-# INLINABLE foldl #-}

-- | TODO: Document
--
withFoldl :: Foldl a b -> L r a b -> r
withFoldl (Foldl h z k) f = f h z k
{-# INLINABLE withFoldl #-}

prefix :: a -> Foldl a b -> Foldl a b
prefix a = flip run a . duplicate
{-# INLINABLE prefix #-}

{-
type IndexedFoldl i a b = Foldl (i, a) b

ifoldl :: FoldableWithKey f => IndexedFoldl (Key f) a b -> f a -> b
ifoldl (Foldl step begin done) as = foldrWithKey cons done as begin
  where
    cons i a k x = k $! step x (i, a)

{-| Convert a strict left 'Fold' into a scan

    >>> L.scan L.length [1..5]
    [0,1,2,3,4,5]
-}
scan :: Foldl a b -> [a] -> [b]
scan (Foldl step begin done) as = foldr cons nil as begin
  where
    nil      x = done x:[]
    cons a k x = done x:(k $! step x a)
{-# INLINE scan #-}


-}

-- | Convert a `Foldl` into a prescan for any `Traversable` type
--
--  \"Prescan\" means that the lastDef element of the scan is not included
--
prescan :: Traversable f => Foldl a b -> f a -> f b
prescan (Foldl step begin done) as = bs
  where
    step' x a = (x', b)
      where
        x' = step x a
        b  = done x
    (_, bs) = mapAccumL step' begin as
{-# INLINE prescan #-}

-- | Convert a `Foldl` into a postscan for any `Traversable` type
--
--  \"Postscan\" means that the first element of the scan is not included
--
postscan :: Traversable f => Foldl a b -> f a -> f b
postscan (Foldl step begin done) as = bs
  where
    step' x a = (x', b)
      where
        x' = step x a
        b  = done x'
    (_, bs) = mapAccumL step' begin as
{-# INLINE postscan #-}

---------------------------------------------------------------------
-- Folds
---------------------------------------------------------------------

-- | Foldl all values into a list
list :: Foldl a [a]
list = Foldl (\x a -> x . (a:)) id ($ [])
{-# INLINABLE list #-}

-- | Foldl all values into a list, in reverse order
revList :: Foldl a [a]
revList = Foldl (\x a -> a:x) [] id
{-# INLINABLE revList #-}

-- | Convert a \"@mconcats@\" to a 'Fold'
mconcat :: Monoid m => (a -> m) -> (m -> b) -> Foldl a b
mconcat to = Foldl (\x a -> mappend x (to a)) mempty
{-# INLINABLE mconcat #-}

-- | Return the result of a step function.
--
-- Results in a 'Nothing' value for empty containers.
--
stepMay :: (a -> a -> a) -> Foldl a (Maybe a)
stepMay step = Foldl step_ M'.Nothing lazy
  where
    step_ mx a = M'.Just (case mx of
        M'.Nothing -> a
        M'.Just x -> step x a)
{-# INLINABLE stepMay #-}

stepDef :: a -> (a -> a -> a) -> Foldl a a
stepDef a step = maybe a id <$> stepMay step
{-# INLINABLE stepDef #-}
{-
-- | Return the sum of all elements.
--
sum :: (Sum-Monoid) a => Foldl a a
sum = sumWith id
{-# INLINABLE sum #-}

-- | Return the sum of all elements.
--
sumWith :: (Sum-Monoid) b => (a -> b) -> Foldl a b
sumWith f = Foldl (\x y -> x + f y) zero id
{-# INLINABLE sumWith #-}

-- | Return the product of all elements.
--
product :: (Product-Monoid) a => Foldl a a
product = productWith id
{-# INLINABLE product #-}

-- | Return the product of all elements.
--
productWith :: (Product-Monoid) b => (a -> b) -> Foldl a b
productWith f = Foldl (\x y -> x * f y) one id
{-# INLINABLE productWith #-}
-}

-- | Return the first element of a collection.
--
-- Returns a default if the container is empty.
--
headDef :: a -> Foldl a a
headDef a = stepDef a const
{-# INLINABLE headDef #-}

-- | Return the last element of a collection.
--
-- Returns a default if the container is empty.
--
lastDef :: a -> Foldl a a
lastDef a = stepDef a (flip const)
{-# INLINABLE lastDef #-}

-- | Return the maximumDef element of a collection.
--
-- Returns a default if the container is empty.
--
maximumDef :: Ord a => a ->Foldl a a
maximumDef a = stepDef a max
{-# INLINABLE maximumDef #-}

-- | Return the maximumDef element of a collection wrt a comparator.
--
-- Returns a default if the container is empty.
--
maximumByDef :: (a -> a -> Ordering) -> a -> Foldl a a
maximumByDef cmp a = stepDef a max'
  where
    max' x y = case cmp x y of
        GT -> x
        _  -> y
{-# INLINABLE maximumByDef #-}

-- | Return the minimumDef element of a collection.
--
-- Returns a default if the container is empty.
--
minimumDef :: Ord a => a -> Foldl a a
minimumDef a = stepDef a min
{-# INLINABLE minimumDef #-}

-- | Return the minimumDef element of a collection wrt a comparator.
--
-- Returns a default if the container is empty.
--
minimumByDef :: (a -> a -> Ordering) -> a -> Foldl a a
minimumByDef cmp a = stepDef a min'
  where
    min' x y = case cmp x y of
        GT -> y
        _  -> x
{-# INLINABLE minimumByDef #-}

---------------------------------------------------------------------
-- Instances
---------------------------------------------------------------------

-- | Convert 'Maybe'' to 'Maybe'
lazy :: M'.Maybe a -> Maybe a
lazy  M'.Nothing = Nothing
lazy (M'.Just a) = Just a
{-# INLINABLE lazy #-}

-- Comonad instances

extract :: Foldl a b -> b
extract (Foldl _ z k) = k z

duplicate :: Foldl a b -> Foldl a (Foldl a b)
duplicate (Foldl h z k) = Foldl h z (flip (Foldl h) k)

--extend :: (Foldl a b -> c) -> Foldl a b -> Foldl a c
--extend f (Foldl h z k) = Foldl h z (f . flip (Foldl h) k)

instance Functor (Foldl a) where
    fmap f (Foldl step begin done) = Foldl step begin (f . done)
    {-# INLINE fmap #-}

instance Profunctor Foldl where
  rmap = fmap
  lmap f (Foldl step begin done) = Foldl step' begin done
    where
      step' x a = step x (f a)

instance Choice Foldl where
  right' (Foldl step begin done) = Foldl (liftA2 step) (Right begin) (fmap done)
  {-# INLINE right' #-}

{-
instance Comonad (Foldl a) where
    extract (Foldl _ begin done) = done begin
    {-#  INLINE extract #-}

    duplicate (Foldl step begin done) = Foldl step begin (\x -> Foldl step x done)
    {-#  INLINE duplicate #-}
-}

instance Applicative (Foldl a) where
    pure b    = Foldl (\() _ -> ()) () (\() -> b)
    {-# INLINE pure #-}

    (Foldl stepL beginL doneL) <*> (Foldl stepR beginR doneR) =
        let step (xL :!: xR) a = (stepL xL a) :!: (stepR xR a)
            begin = beginL :!: beginR
            done (xL :!: xR) = doneL xL (doneR xR)
        in  Foldl step begin done
    {-# INLINE (<*>) #-}

instance Distributive (Foldl a) where

  distribute z = Foldl (\fm a -> fmap (prefix a) fm) z (fmap extract)

instance Functor.Representable (Foldl a) where

  type Rep (Foldl a) = [a]

  index = cosieve

  tabulate = cotabulate

instance Cosieve Foldl [] where

  cosieve (Foldl k0 h0 z0) as0 = go k0 h0 z0 as0
    where
      go _ z k [] = k z
      go h z k (a : as) = go h (h z a) k as

instance Closed Foldl where

  closed (Foldl h z k) = Foldl (liftA2 h) (pure z) (\f x -> k (f x))

instance Costrong Foldl where

  unfirst = unfirstCorep

  unsecond = unsecondCorep

instance Corepresentable Foldl where

  type Corep Foldl = []

  cotabulate f = Foldl (flip (:)) [] (f . reverse)

instance Monad (Foldl a) where

  m >>= f = Foldl (flip (:)) [] (\xs -> flip foldl xs . f) <*> m

instance MonadReader [a] (Foldl a) where

  ask = askRep

  local = localRep

instance MonadFix (Foldl a) where
  mfix = mfixRep

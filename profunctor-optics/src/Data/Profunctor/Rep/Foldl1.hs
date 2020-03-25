{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE Safe                      #-}
{-# LANGUAGE RankNTypes                #-}

module Data.Profunctor.Rep.Foldl1 (
  -- * Foldl1
    type L1
  , Foldl1 (..)
  , run1
  , step
  , foldl1
  , withFoldl1
  , prefix1
  , intersperse1
  -- * Folds
  , list1
  , revList1
  , sconcat
  , foldMap1
  --, sum1
  --, sumWith1
  --, prod1
  --, prodWith1
  , head1
  , last1
  , maximum1
  , maximum1By
  , minimum1
  , minimum1By
  -- * Nedl
  , Nedl(..)
  , nedl
  , runNedl
  ) where

import Control.Applicative (liftA2)
import Control.Arrow (Arrow (..), ArrowChoice(..))
import Control.Category (Category)
import Control.Foldl (Fold(..))
import Control.Monad.Fix (MonadFix(..))
import Control.Monad.Reader (MonadReader(..))
import Data.Distributive (Distributive (..))
import Data.Functor.Apply
import Data.Functor.Rep as Functor (Representable (..), askRep, localRep, mfixRep, distributeRep)
import Data.Monoid
import Data.List.NonEmpty as NonEmpty (NonEmpty (..), (<|), fromList)
import Data.Profunctor
import Data.Profunctor.Closed (Closed (..))
import Data.Profunctor.Rep as Profunctor (Corepresentable (..), unfirstCorep, unsecondCorep)
import Data.Profunctor.Sieve (Cosieve (..))
--import Data.Semiring hiding (sum1, sumWith1, product1, productWith1, sum, sumWith, product, productWith)
import qualified Control.Category as C ((.), id)
import qualified Data.List.NonEmpty as NEL
import qualified Data.Semigroup.Foldable as F1 hiding (fold1, foldMap1)

import Prelude as P hiding
  ( null, length, and, or, all, any, sum, foldl1, product, mconcat, elem
  , notElem, lookup, map, either, drop, Num(..), Fractional(..)
  )

type L1 r a b = forall x. (x -> a -> x) -> (a -> x) -> (x -> b) -> r

---------------------------------------------------------------------
-- Foldl1
---------------------------------------------------------------------

data Foldl1 a b = forall x. Foldl1 (x -> a -> x) (a -> x) (x -> b)

-- | Lift a 'Fold' into a 'Foldl1'.
--
-- All of the folds defined in 'Data.Profunctor.Rep.Foldl' may be run as 'Foldl1's.
--
step :: Fold a b -> Foldl1 a b
step (Fold h z k) = Foldl1 h (h z) k

run1 :: Foldl1 a b -> a -> b
run1 (Foldl1 _ z k) a = k (z a)

foldl1 :: F1.Foldable1 f => Foldl1 a b -> f a -> b
foldl1 f = cosieve f . F1.toNonEmpty

withFoldl1 :: Foldl1 a b -> L1 r a b -> r
withFoldl1 (Foldl1 h z k) f = f h z k

prefix1 :: a -> Foldl1 a b -> Foldl1 a b
prefix1 a (Foldl1 h z k) = Foldl1 h (h (z a)) k

intersperse1 :: a -> Foldl1 a b -> Foldl1 a b
intersperse1 a (Foldl1 h z k) = Foldl1 (\x b -> (h $! h x a) b) z k

---------------------------------------------------------------------
-- Non-empty folds
---------------------------------------------------------------------

-- | Fold all values into a non-empty list.
--
-- @
-- 'fold1' 'list1' = id
-- @
--
list1 :: Foldl1 a (NonEmpty a)
list1 = Foldl1 (\as a -> as <> nedl a) nedl runNedl 
{-# INLINABLE list1 #-}

-- | Fold all values into a non-empty list, in reverse order.
--
revList1 :: Foldl1 a (NonEmpty a)
revList1 = Foldl1 (\as a -> nedl a <> as) nedl runNedl
{-# INLINABLE revList1 #-}

-- | Fold all values within a container using a semigroup.
--
sconcat :: Semigroup a => Foldl1 a a
sconcat = Foldl1 (<>) id id
{-# INLINABLE sconcat #-}

-- | Fold all values within a container using a semigroup.
--
foldMap1 :: Semigroup s => (a -> s) -> (s -> b) -> Foldl1 a b
foldMap1 to = Foldl1 (\x a -> x <> (to a)) to
{-# INLINABLE foldMap1 #-}

{-
-- | Return the sum of all elements in a non-empty container.
--
sum1 :: (Sum-Semigroup) a => Foldl1 a a
sum1 = sumWith1 id
{-# INLINABLE sum1 #-}

-- | Return the sum of all elements in a non-empty container.
--
sumWith1 :: (Sum-Semigroup) b => (a -> b) -> Foldl1 a b
sumWith1 f = Foldl1 (\x y -> x + f y) f id
{-# INLINABLE sumWith1 #-}

-- | Return the product of all elements in a non-empty container.
--
prod1 :: (Product-Semigroup) a => Foldl1 a a
prod1 = prodWith1 id
{-# INLINABLE prod1 #-}

-- | Return the product of all elements in a non-empty container.
--
prodWith1 :: (Product-Semigroup) b => (a -> b) -> Foldl1 a b
prodWith1 f = Foldl1 (\x y -> x * f y) f id
{-# INLINABLE prodWith1 #-}
-}

-- | Return the first element in a non-empty container.
--
head1 :: Foldl1 a a
head1 = Foldl1 const id id
{-# INLINABLE head1 #-}

-- | Return the last1 element in a non-empty container.
--
last1 :: Foldl1 a a
last1 = Foldl1 (flip const) id id
{-# INLINABLE last1 #-}

-- | Return the maximum1 element in a non-empty container.
--
maximum1 :: Ord a => Foldl1 a a
maximum1 = Foldl1 max id id
{-# INLINABLE maximum1 #-}

-- | Return the maximum1 element with respect to a comparator.
--
maximum1By :: (a -> a -> Ordering) -> Foldl1 a a
maximum1By cmp = Foldl1 max' id id
  where
    max' x y = case cmp x y of
        GT -> x
        _  -> y
{-# INLINABLE maximum1By #-}

-- | Return the minimum1 element in a non-empty container.
--
minimum1 :: Ord a => Foldl1 a a
minimum1 = Foldl1 min id id
{-# INLINABLE minimum1 #-}

-- | Return the minimum1 element with respect to a comparator.
--
minimum1By :: (a -> a -> Ordering) -> Foldl1 a a
minimum1By cmp = Foldl1 min' id id
  where
    min' x y = case cmp x y of
        GT -> y
        _  -> x
{-# INLINABLE minimum1By #-}

------------------------------------------------------------------------------
-- Nedl 
------------------------------------------------------------------------------

-- | A non-empty difference list.
newtype Nedl a = Nedl { unNedl :: [a] -> NEL.NonEmpty a }

instance Semigroup (Nedl a) where
  Nedl f <> Nedl g = Nedl (f . NEL.toList . g)

nedl :: a -> Nedl a
nedl a = Nedl (a :|)

runNedl :: Nedl a -> NonEmpty a
runNedl = flip unNedl []

---------------------------------------------------------------------
-- Foldl1 instances
---------------------------------------------------------------------

{-
instance (Sum-Semigroup) b => Semigroup (Sum (Foldl1 a b)) where

    (<>) = liftA2 $ liftA2 (+)

instance (Product-Semigroup) b => Semigroup (Product (Foldl1 a b)) where

    (<>) = liftA2 $ liftA2 (*)

instance Presemiring b => Presemiring (Foldl1 a b)
-}

instance Functor (Foldl1 a) where

  fmap f (Foldl1 h z k) = Foldl1 h z (f . k)

  b <$ _ = pure b

instance Apply (Foldl1 a) where

  (<.>) = (<*>)

instance Applicative (Foldl1 a) where

  pure x = Foldl1 (\() _ -> ()) (\_ -> ()) (\() -> x)

  Foldl1 hf zf kf <*> Foldl1 ha za ka =
    Foldl1
      (\(x, y) a -> (hf x a, ha y a))
      (\a -> (zf a, za a))
      (\(x, y) -> kf x (ka y))

  (<*) m _ = m

  _ *> m = m

instance Category Foldl1 where

  id = arr id

  Foldl1 h z k . Foldl1 h' z' k' = Foldl1 h'' z'' (\(b, _) -> k b)
    where
      z'' a = (z (k' b), b) where b = z' a
      h'' (c, d) a = (h c (k' d'), d') where d' = h' d a

instance Profunctor Foldl1 where

  dimap f g (Foldl1 h z k) = Foldl1 (\a -> h a . f) (z . f) (g . k)

  lmap f (Foldl1 h z k) = Foldl1 (\a -> h a . f) (z . f) k

  rmap g (Foldl1 h z k) = Foldl1 h z (g . k)

instance Strong Foldl1 where

  first' = first

  second' = second

instance Choice Foldl1 where

  left' = left

  right' = right

instance Closed Foldl1 where

  closed (Foldl1 h z k) = Foldl1 (liftA2 h) (fmap z) (\f x -> k (f x))

instance Cosieve Foldl1 NonEmpty where

  cosieve = Functor.index

instance Costrong Foldl1 where

  unfirst = unfirstCorep

  unsecond = unsecondCorep

instance Corepresentable Foldl1 where

  type Corep Foldl1 = NonEmpty

  cotabulate = Functor.tabulate

instance Distributive (Foldl1 a) where

  distribute = distributeRep

instance Functor.Representable (Foldl1 a) where

  type Rep (Foldl1 a) = NonEmpty a

  tabulate f = Foldl1 (flip (:)) pure (f . NonEmpty.fromList . P.reverse)

  index (Foldl1 h z k) (a :| as) = k (foldl h (z a) as)

instance Arrow Foldl1 where

  arr h = Foldl1 (\_ a -> a) id h

  first (Foldl1 h z k) = Foldl1 h' (first z) (first k)
    where
      h' (a, _) (c, b) = (h a c, b)

  second (Foldl1 h z k) = Foldl1 h' (second z) (second k)
    where
      h' (_, b) (a, c) = (a, h b c)

  Foldl1 h z k *** Foldl1 h' z' k' = Foldl1 h'' (z *** z') (k *** k')
    where
      h'' (a, b) (c, d) = (h a c, h' b d)

  Foldl1 h z k &&& Foldl1 h' z' k' = Foldl1 h'' (z &&& z') (k *** k')
    where
      h'' (c, d) a = (h c a, h' d a)

instance ArrowChoice Foldl1 where

  left (Foldl1 h z k) = Foldl1 h' (left' `id` z) (left' `id` k) where
    h' (Left x) (Left y) = Left (h x y)
    h' (Right c) _ = Right c
    h' _ (Right c) = Right c
  {-# INLINE left #-}

  right (Foldl1 h z k) = Foldl1 h' (right' `id` z) (right' `id` k) where
    h' (Right x) (Right y) = Right (h x y)
    h' (Left c) _ = Left c
    h' _ (Left c) = Left c
  {-# INLINE right #-}

instance Monad (Foldl1 a) where

  m >>= f = Foldl1 (flip (<|)) pure (\xs -> flip foldl1 xs . f) <*> m

instance MonadReader (NonEmpty a) (Foldl1 a) where

  ask = askRep

  local = localRep

instance MonadFix (Foldl1 a) where
  mfix = mfixRep

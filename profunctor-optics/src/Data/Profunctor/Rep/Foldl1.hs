{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE RankNTypes                #-}

module Data.Profunctor.Rep.Foldl1 (
  -- * Foldl1
    Foldl1 (..)
  , Unfoldl1 (..)
  , run1
  , step
  , foldl1
  , build1
  , withFoldl1
  , prefix1
  , intersperse1
  -- * FoldlM1
  , FoldlM1 (..)
  , UnfoldlM1 (..)
  -- * Folds
  , list1
  , revList1
  , sconcat
  --, sum1
  --, sumWith1
  --, prod1
  --, prodWith1
  , head
  , last
  , maximum
  , maximumBy
  , minimum
  , minimumBy
  -- * Unfolds
  , foldable1
  , nonNull
  -- * Nedl
  , Nedl(..)
  , nedl
  , runNedl
  ) where

import Control.Applicative (liftA2)
import Control.Arrow (Arrow (..), ArrowChoice(..))
import Control.Category (Category)
import Control.Monad.Fix (MonadFix(..))
import Control.Monad.Zip (MonadZip(..))
import Control.Monad.Reader (MonadReader(..))
import Data.Distributive (Distributive (..))
import Data.Functor.Apply
--import Data.Functor.Rep as Functor (Representable (..), askRep, localRep, mfixRep, distributeRep)
import Data.Monoid
import Data.List.NonEmpty as NonEmpty (NonEmpty (..), (<|), fromList)
import Data.Profunctor
import Data.Profunctor.Closed (Closed (..))
import qualified Data.Profunctor.Rep.Foldl as L
import Data.Profunctor.Rep as Profunctor (Corepresentable (..), unfirstCorep, unsecondCorep)
import Data.Profunctor.Sieve (Cosieve (..))
--import Data.Semiring hiding (sum1, sumWith1, product1, productWith1, sum, sumWith, product, productWith)
import qualified Control.Category as C ((.), id)
import qualified Data.List.NonEmpty as NEL
import qualified Data.Semigroup.Foldable as F1 hiding (fold1)
import qualified Data.Foldable as F
import qualified Data.NonNull as NN
import Data.Sequences (IsSequence, LazySequence, Index)
import Data.MonoTraversable (MonoFoldable(..), Element)

import qualified Data.ByteString      as BS
import qualified Data.ByteString.Lazy as BL


import Prelude as P hiding
  ( null, length, and, or, all, any, sum, foldl1, product, mconcat, elem
  , notElem, lookup, map, either, drop, Num(..), Fractional(..)
  , minimum, maximum, last, head
  )

data FoldlM1 m a b = forall x. FoldlM1 (x -> a -> m x) (a -> m x) (x -> m b)

newtype UnfoldlM1 m a = UnfoldlM1 (forall x. (x -> a -> m x) -> (a -> m x) -> m x)
--newtype UnfoldlM1 m a = Unfoldl1 (forall x. (x -> a -> m x) -> m x)

{-
buildM1 :: Monad m => FoldlM1 m a b -> UnfoldlM1 m a -> m b
buildM1 (FoldlM1 h z k) (UnfoldlM1 run) = run h z >>= k

-- | Construct an 'L.Unfoldl' from a 'Data.Foldable1'.
--
foldableM1 :: F1.Foldable1 f => f a -> Unfoldl1 a
foldableM1 f = UnfoldlM1 $ \h z -> F.foldlM' h (z a) as
  where a NEL.:| as = F1.toNonEmpty f
{-# INLINE foldableM1 #-}
-}

---------------------------------------------------------------------
-- Foldl1
---------------------------------------------------------------------

data Foldl1 a b = forall x. Foldl1 (x -> a -> x) (a -> x) (x -> b)

newtype Unfoldl1 a = Unfoldl1 (forall x. (x -> a -> x) -> (a -> x) -> x)

--bytes1 b = Unfoldl1 (\ h _ -> BL.foldl1 h b)

-- | A version of the /build/ function from < http://hackage.haskell.org/package/base-4.12.0.0/docs/src/GHC.Base.html#build base >.
--
build1 :: Foldl1 a b -> Unfoldl1 a -> b
build1 (Foldl1 h z k) (Unfoldl1 run) = k (run h z)
{-# INLINE build1 #-}

-- | Construct an 'L.Unfoldl' from a 'Data.Foldable1'.
--
foldable1 :: F1.Foldable1 f => f a -> Unfoldl1 a
foldable1 f = Unfoldl1 $ \h z -> F.foldl' h (z a) as where a NEL.:| as = F1.toNonEmpty f 
{-# INLINE foldable1 #-}

nonNull :: IsSequence a => NN.NonNull a -> Unfoldl1 (Element a)
nonNull a = Unfoldl1 $ \h z -> ofoldl' h (z e) es where (e, es) = NN.splitFirst a
{-# INLINE nonNull #-}

{-

type Unfoldl1 a = L.Unfoldl a

-- | A version of the /build/ function from < http://hackage.haskell.org/package/base-4.12.0.0/docs/src/GHC.Base.html#build base >.
--
build1 :: Foldl1 a b -> Unfoldl1 a -> a -> b
build1 (Foldl1 h z k) (L.Unfoldl run) a = k (run h $ z a)
{-# INLINE build1 #-}

-- | Construct an 'L.Unfoldl' from a 'Data.Foldable1'.
--
foldable1 :: F1.Foldable1 f => f a -> Unfoldl1 a
foldable1 = L.foldable
{-# INLINE foldable1 #-}

-}

-- | Lift a 'Foldl' into a 'Foldl1'.
--
-- All of the folds defined in 'Data.Profunctor.Rep.Foldl' may be run as 'Foldl1's.
--
step :: L.Foldl a b -> Foldl1 a b
step (L.Foldl h z k) = Foldl1 h (h z) k
{-# INLINABLE step #-}

run1 :: Foldl1 a b -> a -> b
run1 (Foldl1 _ z k) a = k (z a)
{-# INLINABLE run1 #-}

foldl1 :: F1.Foldable1 f => Foldl1 a b -> f a -> b
foldl1 f = cosieve f . F1.toNonEmpty
{-# INLINABLE foldl1 #-}

withFoldl1 :: Foldl1 a b -> (forall x. (x -> a -> x) -> (a -> x) -> (x -> b) -> r) -> r
withFoldl1 (Foldl1 h z k) f = f h z k
{-# INLINABLE withFoldl1 #-}

prefix1 :: a -> Foldl1 a b -> Foldl1 a b
prefix1 a (Foldl1 h z k) = Foldl1 h (h (z a)) k
{-# INLINABLE prefix1 #-}

intersperse1 :: a -> Foldl1 a b -> Foldl1 a b
intersperse1 a (Foldl1 h z k) = Foldl1 (\x b -> (h $! h x a) b) z k
{-# INLINABLE intersperse1 #-}

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
sconcat :: Semigroup s => (a -> s) -> (s -> b) -> Foldl1 a b
sconcat to = Foldl1 (\x a -> x <> (to a)) to
{-# INLINABLE sconcat #-}

-- | Return the first element in a non-empty container.
--
head :: Foldl1 a a
head = Foldl1 const id id
{-# INLINABLE head #-}

-- | Return the last1 element in a non-empty container.
--
last :: Foldl1 a a
last = Foldl1 (flip const) id id
{-# INLINABLE last #-}

-- | Return the maximum element in a non-empty container.
--
maximum :: Ord a => Foldl1 a a
maximum = Foldl1 max id id
{-# INLINABLE maximum #-}

-- | Return the maximum element with respect to a comparator.
--
maximumBy :: (a -> a -> Ordering) -> Foldl1 a a
maximumBy cmp = Foldl1 max' id id
  where
    max' x y = case cmp x y of
        GT -> x
        _  -> y
{-# INLINABLE maximumBy #-}

-- | Return the minimum element in a non-empty container.
--
minimum :: Ord a => Foldl1 a a
minimum = Foldl1 min id id
{-# INLINABLE minimum #-}

-- | Return the minimum element with respect to a comparator.
--
minimumBy :: (a -> a -> Ordering) -> Foldl1 a a
minimumBy cmp = Foldl1 min' id id
  where
    min' x y = case cmp x y of
        GT -> y
        _  -> x
{-# INLINABLE minimumBy #-}

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

  cosieve (Foldl1 h z k) (a :| as) = k (foldl h (z a) as)

instance Costrong Foldl1 where

  unfirst = unfirstCorep

  unsecond = unsecondCorep

instance Corepresentable Foldl1 where

  type Corep Foldl1 = NonEmpty

  cotabulate f = Foldl1 (flip (:)) pure (f . NonEmpty.fromList . P.reverse)

instance Distributive (Foldl1 a) where

  distribute wf = cotabulate (\k -> fmap (`cosieve` k) wf)


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

  ask = cotabulate id

  local f m = cotabulate (cosieve m . f)

instance MonadFix (Foldl1 a) where

  mfix = cotabulate . mfix . fmap cosieve

instance MonadZip (Foldl1 a) where

  mzipWith = liftA2

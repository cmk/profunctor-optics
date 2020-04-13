{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE ViewPatterns             #-}
{-# LANGUAGE StandaloneDeriving        #-}

module Data.Profunctor.Rep.Fold1 (
  -- * Unfold1
    Unfold1 (..)
  , forwards
  , toUnfold
  , snoc
  , cons
  , head
  , last
  -- * UnfoldM1
  -- , UnfoldM1 (..)
  -- * Fold1
  , Fold1 (..)
  , run1
  , step
  , fold1
  , prefix1
  , intersperse1
  -- * FoldM1
  -- , FoldM1 (..)
  -- * Folds
  , list1
  , revList1
  , sconcat
  , sconcats
  , maximum
  , maximumBy
  , minimum
  , minimumBy
  -- * Nedl
  , Nedl(..)
  , nedl
  , runNedl
  ) where

import Control.Applicative (liftA2)
import Control.Arrow (Arrow (..), ArrowChoice(..))
import Control.Category (Category)
import Control.Foldl (Fold(..))
import Control.Monad (ap)
import Control.Monad.Fix (MonadFix(..))
import Control.Monad.Reader (MonadReader(..))
import Data.Distributive (Distributive (..))
import Data.Functor.Apply
import Data.Functor.Alt
--import Data.Functor.Coapply
import Data.Monoid hiding (Alt)
import Data.List.NonEmpty as NonEmpty (NonEmpty (..), (<|), fromList)
import Data.Profunctor
import Data.Profunctor.Closed (Closed (..))
import Data.Profunctor.Rep as Profunctor (Corepresentable (..), unfirstCorep, unsecondCorep)
import Data.Profunctor.Sieve (Cosieve (..))
import qualified Control.Category as C ((.), id)

import qualified Data.Foldable as F
import qualified Data.List.NonEmpty as NEL
import qualified Data.Semigroup.Foldable as F1 hiding (fold1)
import qualified Data.Profunctor.Rep.Fold as L

import Prelude as P hiding
  ( null, length, and, or, all, any, sum, fold1, product, mconcat, elem
  , notElem, lookup, map, either, drop, Num(..), Fractional(..), minimum
  , maximum, head, last
  )

--import Control.Scanl (Scan(..),ScanM(..))
--import qualified Control.Scanl as SL

---------------------------------------------------------------------
-- Unfold1
---------------------------------------------------------------------

newtype Unfold1 a = Unfold1 { runfold1 :: forall x. (x -> a -> x) -> (a -> x) -> x }

forwards :: F1.Foldable1 f => f a -> Unfold1 a
forwards (F1.toNonEmpty -> a :| as) = Unfold1 $ \ h z -> F.foldl' h (z a) as

toUnfold :: Unfold1 a -> L.Unfold a
toUnfold (Unfold1 u) = L.Unfold $ \ h x -> u h (const x)

--reverse (Unfold u) = Unfold $ \ h -> u (\ f a -> f . flip h a) id
--backwards :: F1.Foldable1 f => f a -> Unfold1 a

snoc :: a -> Unfold1 a -> Unfold1 a
snoc a (Unfold1 u) = Unfold1 $ \ h z -> h (u h z) (id a) --  (\_ -> a)

cons :: Unfold1 a -> a -> Unfold1 a
cons (Unfold1 u) a = Unfold1 $ \ h z -> u h (h (z a))

head :: Unfold1 a -> a
head (Unfold1 u) = u const id

last :: Unfold1 a -> a
last (Unfold1 u) = u (flip const) id

--reverse :: Unfold1 a -> Unfold1 a

--purely_ :: (forall x . (x -> a -> x) -> (a -> x) -> x) -> Scan a b -> b
--purely_ u = flip cosieve $ F1.toNonEmpty (Unfold1 u)

---------------------------------------------------------------------
-- UnfoldM1
---------------------------------------------------------------------

-- newtype UnfoldM1 m a = UnfoldM1 { runfoldlM1 :: forall x. (x -> a -> m x) -> (a -> m x) -> m x }


---------------------------------------------------------------------
-- Fold1
---------------------------------------------------------------------

data Fold1 a b = forall x. Fold1 (x -> a -> x) (a -> x) (x -> b)

-- | Lift a 'Fold' into a 'Fold1'.
--
-- All of the folds defined in 'Data.Profunctor.Rep.Fold' may be run as 'Fold1's.
--
step :: Fold a b -> Fold1 a b
step (Fold h z k) = Fold1 h (h z) k

--scan :: Traversable f => Fold1 a b -> f a -> f b
--scan (toScan -> Scan step begin) as = fst $ runState (traverse step as) begin

run1 :: Fold1 a b -> a -> b
run1 (Fold1 _ z k) a = k (z a)

fold1 :: F1.Foldable1 f => Fold1 a b -> f a -> b
fold1 f = cosieve f . F1.toNonEmpty

folds1 :: Fold1 a b -> Unfold1 a -> b
folds1 = fold1

prefix1 :: a -> Fold1 a b -> Fold1 a b
prefix1 a (Fold1 h z k) = Fold1 h (h (z a)) k

intersperse1 :: a -> Fold1 a b -> Fold1 a b
intersperse1 a (Fold1 h z k) = Fold1 (\x b -> (h $! h x a) b) z k

---------------------------------------------------------------------
-- FoldM1
---------------------------------------------------------------------

-- data FoldM1 m a b = forall x. FoldM1 (x -> a -> m x) (a -> m x) (x -> m b)

--foldM1 :: Monad m => F1.Foldable1 f => FoldM1 m a b -> f a -> m b
--foldM1 (ScanM f z) (F1.toNonEmpty -> (a :| as)) = fmap P.last $ z >>= evalStateT (traverse f $ a:as)

--foldsM1 :: Monad m => FoldM1 a b -> UnfoldM1 m a -> m b
--foldsM1 s (UnfoldM1 u) = withMealy s $ \h z k -> k <$> u (\x a -> pure $ h x a) (pure . z)

---------------------------------------------------------------------
-- Non-empty folds
---------------------------------------------------------------------

-- | Fold all values into a non-empty list.
--
-- @
-- 'fold1' 'list1' = id
-- @
--
list1 :: Fold1 a (NonEmpty a)
list1 = Fold1 (\as a -> as <> nedl a) nedl runNedl 
{-# INLINABLE list1 #-}

-- | Fold all values into a non-empty list, in reverse order.
--
revList1 :: Fold1 a (NonEmpty a)
revList1 = Fold1 (\as a -> nedl a <> as) nedl runNedl
{-# INLINABLE revList1 #-}

-- | Fold all values within a container using a semigroup.
--
sconcat :: Semigroup a => Fold1 a a
sconcat = Fold1 (<>) id id
{-# INLINABLE sconcat #-}

-- | Fold all values within a container using a semigroup.
--
sconcats :: Semigroup s => (a -> s) -> (s -> b) -> Fold1 a b
sconcats f = Fold1 (\x a -> x <> (f a)) f
{-# INLINABLE sconcats #-}

-- | Return the first element in a non-empty container.
--
--head :: Fold1 a a
--head = Fold1 const id id
--{-# INLINABLE head #-}

-- | Return the last element in a non-empty container.
--
--last :: Fold1 a a
--last = Fold1 (flip const) id id
--{-# INLINABLE last #-}

-- | Return the maximum element in a non-empty container.
--
maximum :: Ord a => Fold1 a a
maximum = Fold1 max id id
{-# INLINABLE maximum #-}

-- | Return the maximum element with respect to a comparator.
--
maximumBy :: (a -> a -> Ordering) -> Fold1 a a
maximumBy cmp = Fold1 max' id id
  where
    max' x y = case cmp x y of
        GT -> x
        _  -> y
{-# INLINABLE maximumBy #-}

-- | Return the minimum element in a non-empty container.
--
minimum :: Ord a => Fold1 a a
minimum = Fold1 min id id
{-# INLINABLE minimum #-}

-- | Return the minimum element with respect to a comparator.
--
minimumBy :: (a -> a -> Ordering) -> Fold1 a a
minimumBy cmp = Fold1 min' id id
  where
    min' x y = case cmp x y of
        GT -> y
        _  -> x
{-# INLINABLE minimumBy #-}

---------------------------------------------------------------------
-- Unfold1 instances
---------------------------------------------------------------------

deriving instance Functor Unfold1

instance Apply Unfold1 where
  (<.>) = ap 

instance Applicative Unfold1 where
  pure x = Unfold1 (\h z -> h (z x) x)
  (<*>) = ap 

instance Alt Unfold1 where
  (<!>) (Unfold1 l) (Unfold1 r) = Unfold1 (\h z -> r h $ const (l h z))
  {-# INLINE (<!>) #-}

instance Monad Unfold1 where
  return = pure

  (>>=) (Unfold1 u) f = Unfold1 $
    \h z -> let h' x a = runfold1 (f a) h (const x)
                k a = NEL.head $ F1.toNonEmpty (f a)
             in u h' (z . k)

instance Semigroup (Unfold1 a) where
  (<>) = (<!>)

instance Foldable Unfold1 where
  foldMap f (Unfold1 u) = u (\x a -> x <> f a) mempty
  {-# INLINE foldMap #-}
  foldl' h z (Unfold1 u) = u h $ const z
  {-# INLINE foldl' #-}

instance F1.Foldable1 Unfold1 where
  foldMap1 f (Unfold1 u) = u (\x a -> x <> f a) f

instance Eq a => Eq (Unfold1 a) where
  (==) left right = F.toList left == F.toList right

instance Show a => Show (Unfold1 a) where
  show = show . F.toList


---------------------------------------------------------------------
-- Fold1 instances
---------------------------------------------------------------------


instance Functor (Fold1 a) where

  fmap f (Fold1 h z k) = Fold1 h z (f . k)

  b <$ _ = pure b

instance Apply (Fold1 a) where

  (<.>) = (<*>)

instance Applicative (Fold1 a) where

  pure x = Fold1 (\() _ -> ()) (\_ -> ()) (\() -> x)

  Fold1 hf zf kf <*> Fold1 ha za ka =
    Fold1
      (\(x, y) a -> (hf x a, ha y a))
      (\a -> (zf a, za a))
      (\(x, y) -> kf x (ka y))

  (<*) m _ = m

  _ *> m = m

instance Category Fold1 where

  id = arr id

  Fold1 h z k . Fold1 h' z' k' = Fold1 h'' z'' (\(b, _) -> k b)
    where
      z'' a = (z (k' b), b) where b = z' a
      h'' (c, d) a = (h c (k' d'), d') where d' = h' d a

instance Profunctor Fold1 where

  dimap f g (Fold1 h z k) = Fold1 (\a -> h a . f) (z . f) (g . k)

  lmap f (Fold1 h z k) = Fold1 (\a -> h a . f) (z . f) k

  rmap g (Fold1 h z k) = Fold1 h z (g . k)

instance Strong Fold1 where

  first' = first

  second' = second

instance Choice Fold1 where

  left' = left

  right' = right

instance Distributive (Fold1 a) where

  distribute wf = cotabulate (\k -> fmap (`cosieve` k) wf)

instance Closed Fold1 where

  closed (Fold1 h z k) = Fold1 (liftA2 h) (fmap z) (\f x -> k (f x))

instance Cosieve Fold1 NonEmpty where

  cosieve (Fold1 h z k) (a :| as) = k (F.foldl' h (z a) as)

instance Costrong Fold1 where

  unfirst = unfirstCorep

  unsecond = unsecondCorep

instance Corepresentable Fold1 where

  type Corep Fold1 = NonEmpty

  cotabulate f = Fold1 (flip (:)) pure (f . NonEmpty.fromList . P.reverse)

instance Arrow Fold1 where

  arr h = Fold1 (\_ a -> a) id h

  first (Fold1 h z k) = Fold1 h' (first z) (first k)
    where
      h' (a, _) (c, b) = (h a c, b)

  second (Fold1 h z k) = Fold1 h' (second z) (second k)
    where
      h' (_, b) (a, c) = (a, h b c)

  Fold1 h z k *** Fold1 h' z' k' = Fold1 h'' (z *** z') (k *** k')
    where
      h'' (a, b) (c, d) = (h a c, h' b d)

  Fold1 h z k &&& Fold1 h' z' k' = Fold1 h'' (z &&& z') (k *** k')
    where
      h'' (c, d) a = (h c a, h' d a)

instance ArrowChoice Fold1 where

  left (Fold1 h z k) = Fold1 h' (left' `id` z) (left' `id` k) where
    h' (Left x) (Left y) = Left (h x y)
    h' (Right c) _ = Right c
    h' _ (Right c) = Right c
  {-# INLINE left #-}

  right (Fold1 h z k) = Fold1 h' (right' `id` z) (right' `id` k) where
    h' (Right x) (Right y) = Right (h x y)
    h' (Left c) _ = Left c
    h' _ (Left c) = Left c
  {-# INLINE right #-}

instance Monad (Fold1 a) where

  m >>= f = Fold1 (flip (<|)) pure (\xs -> flip fold1 xs . f) <*> m

instance MonadReader (NonEmpty a) (Fold1 a) where

  ask = cotabulate id

  local f m = cotabulate (cosieve m . f)

instance MonadFix (Fold1 a) where

  mfix = cotabulate . mfix . fmap cosieve


---------------------------------------------------------------------
-- Orphan Scan instances
---------------------------------------------------------------------

{-

mealy :: (x -> a -> x) -> (a -> x) -> (x -> b) -> Scan a b
mealy h z k = cotabulate $ \(a :| as) -> k (F.foldl' h (z a) as)

withMealy :: Scan a b -> (forall x. (x -> a -> x) -> (a -> x) -> (x -> b) -> r) -> r
withMealy s f = f (flip (:)) pure (cosieve s . NonEmpty.fromList . P.reverse) 
{-# INLINABLE withMealy #-}

fold1 :: F1.Foldable1 f => Scan a b -> f a -> b
fold1 f = cosieve f . F1.toNonEmpty

folds1 :: Scan a b -> Unfold1 a -> b
folds1 = fold1

toScan :: Fold1 a b -> Scan a b
toScan = cotabulate . cosieve

fromScan :: Scan a b -> Fold1 a b
fromScan = cotabulate . cosieve

instance Monad (Scan a) where
  m >>= f = cotabulate $ \a -> cosieve (f (cosieve m a)) a

instance Strong Scan where
  first' = first

  second' = second

instance Choice Scan where

  left' (Scan f x) = Scan (runKleisli . left' $ Kleisli f) x
 
  right' (Scan f x) = Scan (runKleisli . right' $ Kleisli f) x

instance Closed Scan where

  closed = closedCorep

instance Costrong Scan where

  unfirst = unfirstCorep

  unsecond = unsecondCorep

--instance Distributive (Scan a) where

instance Cosieve Scan NonEmpty where
  -- >>> s = cotabulate F.toList :: Scan Int [Int]
  -- >>> cosieve s $ 0 :| [1..3]
  -- [0,1,2,3]
  cosieve (Scan f z) (a :| as) = P.last $ evalState (traverse f $ a:as) z 

instance Corepresentable Scan where
  type Corep Scan = NonEmpty

  cotabulate f = Scan go [] where -- TODO optimize
    go a = state $ \as -> (f . NonEmpty.fromList $ P.reverse (a:as), a:as) 

instance MonadFix (Scan a) where

  mfix = cotabulate . mfix . fmap cosieve
-}

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

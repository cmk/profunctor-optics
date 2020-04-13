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
{-# LANGUAGE ViewPatterns              #-}
{-# LANGUAGE PatternSynonyms           #-}
{-# LANGUAGE StandaloneDeriving        #-}

module Data.Profunctor.Rep.Fold1 where
{- (
  -- * Unfold1
    Unfold1 (..)
  , unfoldl
  , unfoldr
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
  , scan
  , fold1
  , purely_
  , prefix1
  , intersperse1
  -- * FoldM1
  -- , FoldM1 (..)
  -- * Folds
  , list1
  , revList1
  , sconcat
  , foldMap1
  , maximum
  , maximumBy
  , minimum
  , minimumBy
  -- * Nedl
  , Nedl(..)
  , nedl
  , runNedl
  ) where
-}

import Control.Applicative (liftA2)
import Control.Coapplicative
import Control.Arrow (Arrow (..), ArrowChoice(..),Kleisli(..))
import Control.Category (Category)
import Control.Foldl (Fold(..))
import Control.Scanl (Scan(..),ScanM(..))
import Control.Monad (ap)
import Control.Monad.Fix (MonadFix(..))
import Control.Monad.Reader (MonadReader(..))
import Control.Monad.State.Strict -- (MonadReader(..))
import Control.Monad.IO.Unlift
import Data.Distributive (Distributive (..))
import Data.Functor.Apply
import Data.Functor.Coapply
import Data.Functor.Alt
import Data.Functor.Identity
import Data.Semigroup.Traversable
import Data.Monoid hiding (Alt)
import Data.List.NonEmpty as NonEmpty (NonEmpty (..), (<|), fromList)
import Data.Profunctor
import Data.Profunctor.Closed (Closed (..))
import Data.Profunctor.Rep as Profunctor (Corepresentable (..), unfirstCorep, unsecondCorep,closedCorep)
import Data.Profunctor.Sieve (Cosieve (..))
import Data.Traversable (mapAccumL)
import qualified Control.Category as C ((.), id)

import qualified Data.Bifunctor as B
import qualified Data.Foldable as F
import qualified Data.List.NonEmpty as L1
import qualified Data.Semigroup.Foldable as F1 hiding (fold1)
import qualified Data.Profunctor.Rep.Fold as L

import Prelude as P hiding
  ( null, length, and, or, all, any, sum, fold1, product, mconcat, elem
  , notElem, lookup, map, either, drop, Num(..), Fractional(..), minimum
  , maximum, head, last, tail, init
  )
import qualified Prelude as P 
--import Control.Scanl (Scan(..),ScanM(..))
--import qualified Control.Scanl as SL
import qualified Control.Foldl as FL

{-todo
uncons :: [a] -> Maybe (a, [a]) 
uncons :: Unfold1 a -> (a, Unfold a) 

scanl :: (b -> a -> b) -> b -> [a] -> [b] 
scanl1 :: (a -> a -> a) -> [a] -> [a] 
scanr :: (a -> b -> b) -> b -> [a] -> [b] 
scanr1 :: (a -> a -> a) -> [a] -> [a] 

iterate :: (a -> a) -> a -> [a] 
repeat :: a -> [a] 
replicate :: Int -> a -> [a] 
cycle :: [a] -> [a] 

take :: Int -> [a] -> [a] 
drop :: Int -> [a] -> [a] 
span :: (a -> Bool) -> [a] -> ([a], [a]) 
break :: (a -> Bool) -> [a] -> ([a], [a]) 
stripPrefix :: Eq a => [a] -> [a] -> Maybe [a] 
isPrefixOf :: Eq a => [a] -> [a] -> Bool
intersperse :: a -> [a] -> [a]

sort :: Ord a => [a] -> [a] 
sortOn :: Ord b => (a -> b) -> [a] -> [a]
sortBy :: (a -> a -> Ordering) -> [a] -> [a]
insertBy :: (a -> a -> Ordering) -> a -> [a] -> [a] 
-}


data Fold1 a b = forall x. Fold1 (x -> a -> x) (a -> x) (x -> b)

---------------------------------------------------------------------
-- Unfold1
---------------------------------------------------------------------

type Unfold1 = UnfoldM1 Identity

pattern Unfold1 :: (forall x. (a -> x -> x) -> (a -> x) -> x) -> Unfold1 a
pattern Unfold1 a <- (runfoldr -> a) where Unfold1 a = unfold1 a

newtype UnfoldM1 m a = UnfoldM1 ( forall x. (a -> x -> m x) -> (a -> m x) -> m x )

---------------------------------------------------------------------
-- Introduction
---------------------------------------------------------------------

-- | Obtain an 'Unfold1' from a left-folding continuation.
--
unfold1 :: (forall x. (a -> x -> x) -> (a -> x) -> x) -> Unfold1 a
unfold1 f = UnfoldM1 $ \h z -> Identity $ f (\a x -> runIdentity $ h a x) (runIdentity . z)

-- >>> F.foldr (:) [] $ (L1.unfoldr1 $ 0 :| [1..3])
-- [0,1,2,3]
unfoldr1 :: F1.Foldable1 f => f a -> Unfold1 a
unfoldr1 ((L1.init &&& L1.last) . F1.toNonEmpty -> (as, a)) = Unfold1 $ \h z -> F.foldr h (z a) as

--Unfold1 $ \ h z -> F.foldr h (z a) as

unfoldl1 :: F1.Foldable1 f => f a -> Unfold1 a
unfoldl1 (F1.toNonEmpty -> a :| as) = snoc1 (L.unfoldl as) a 


---------------------------------------------------------------------
-- Elimination
---------------------------------------------------------------------

-- | Run an 'Unfold1'.
--
runfoldr :: Unfold1 a -> (forall x . (a -> x -> x) -> (a -> x) -> x)
runfoldr (UnfoldM1 u) h z = runIdentity $ u (\a x -> Identity $ h a x) (Identity . z)

runfoldl :: Unfold1 a -> (x -> a -> x) -> (a -> x) -> x
runfoldl (Unfold1 u) h = u (\a -> flip h a)

-- | Run an 'UnfoldM1'.
--
runfoldM :: UnfoldM1 m a -> (a -> x -> m x) -> (a -> m x) -> m x
runfoldM (UnfoldM1 u) h z = u h z

-- | Run an 'UnfoldM1 IO' inside 'Control.Monad.IO.Unlift.UnliftIO'.
--
runfoldIO :: MonadUnliftIO m => UnfoldM1 IO a -> (a -> x -> m x) -> (a -> m x) -> m x
runfoldIO (UnfoldM1 u) h z = withRunInIO $ \io -> u (\a x -> io $ h a x) (io . z)

-- | Run an 'Unfold1' with a continuation function.
--
withUnfold :: Unfold1 a -> ((forall x . (a -> x -> x) -> (a -> x) -> x) -> r) -> r
withUnfold u f = f $ runfoldr u

-- | Run an 'UnfoldM1' with a continuation function.
--
withUnfoldM :: UnfoldM1 m a -> ((forall x . (a -> x -> m x) -> (a -> m x) -> m x) -> r) -> r
withUnfoldM u f = f $ runfoldM u

---------------------------------------------------------------------
-- Basic Interface
---------------------------------------------------------------------

infixr 5 `cons`

-- | Prepend a value to an 'Unfold1'.
--
-- >>> L1.cons 4 (L1.unfoldl1 $ 0 :| [1..3])
-- 4 :| [3,2,1,0]
-- 
cons :: a -> Unfold1 a -> Unfold1 a
cons a (Unfold1 u) = Unfold1 $ \ h z -> h a (u h z)

infixl 5 `snoc`,`snoc1`

-- | Append a value to an 'Unfold1'.
--
-- >>> L1.snoc1 (L.unfoldr [1..3]) 4
-- 1 :| [2,3,4]
-- 
snoc1 :: L.Unfold a -> a -> Unfold1 a
snoc1 (L.Unfold u) a = Unfold1 $ \ h z -> u h (z a)

-- | Append a value to an 'Unfold1'.
--
snoc :: Unfold1 a -> a -> Unfold1 a
snoc (Unfold1 u) a = Unfold1 $ \ h z -> u h (\a1 -> h a1 (z a)) 

-- | Append two 'Unfold1's.
--
append :: Unfold1 a -> Unfold1 a -> Unfold1 a
append = (<>)

-- | Retrieve the first element of an 'Unfold1'.
--
head :: Unfold1 a -> a
head (Unfold1 u) = u (flip const) id

-- |
--
-- >>> L1.uncons $ L1.unfoldr1 (0 :| [1..4])
-- (0,[1,2,3,4])
--
uncons :: Unfold1 a -> (a, L.Unfold a) 
uncons = head &&& tail

-- | /O(1)/ Retrieve the last element of an 'Unfold1'.
--
last :: Unfold1 a -> a
last (Unfold1 u) = u const id

-- | /O(1)/ Retrieve the tail of an 'Unfold1'.
--
tail :: Unfold1 a -> L.Unfold a
tail (Unfold1 u) = L.unfold $ \ h z -> u h (const z)

-- λ> L1.init (L1.unfoldl1 $ 0 :| [1..3])
-- [3,2,1]
init :: Unfold1 a -> L.Unfold a
init (Unfold1 u) = L.unfold $ \ h z -> u (\ a f -> h a . f) (flip const) z

unsnoc :: Unfold1 a -> (L.Unfold a, a) 
unsnoc = init &&& last
---------------------------------------------------------------------
-- Unfold1 instances
---------------------------------------------------------------------

deriving instance Functor Unfold1

instance Apply Unfold1 where
  (<.>) = ap 

instance Applicative Unfold1 where
  pure a = Unfold1 (\h z -> h a (z a))
  (<*>) = ap 

instance Alt Unfold1 where
  (<!>) (Unfold1 l) (Unfold1 r) = Unfold1 (\h z -> r h $ const (l h z))
  {-# INLINE (<!>) #-}

instance Coapply Unfold1 where 
  coapply = B.bimap unfoldr1 unfoldr1 . coapply . F1.toNonEmpty

instance Coapplicative Unfold1 where 
  copure = head

--TODO improve
instance Traversable Unfold1 where
  -- |
  -- >>> traverse pure $ unfoldl [1..5]
  -- [1,2,3,4,5]
  traverse f = fmap unfoldr1 . traverse f . F1.toNonEmpty

instance Traversable1 Unfold1 where
  -- |
  -- >>> traverse pure $ unfoldl [1..5]
  -- [1,2,3,4,5]
  traverse1 f = fmap unfoldr1 . traverse1 f . F1.toNonEmpty

instance Monad Unfold1 where
  return = pure

  (>>=) (Unfold1 u) f = Unfold1 $
    \h z -> let h' a x = runfoldr (f a) h (const x)
                k a = head $ f a -- L1.head $ F1.toNonEmpty (f a)
             in u h' (z . k)

instance Semigroup (Unfold1 a) where
  (<>) = (<!>)

instance Foldable Unfold1 where
  --foldMap f u = let (a0, as) = uncons u in L.runfoldr as (\a x -> f a <> x) (f a0)
  foldMap = F1.foldMap1
  {-# INLINE foldMap #-}
  --foldr h z (Unfold1 u) = u h $ const z
  --{-# INLINE foldr #-}

instance F1.Foldable1 Unfold1 where
  foldMap1 f u = let (a0, as) = uncons u in L.runfoldr as (\a x -> f a <> x) (f a0)

instance Eq a => Eq (Unfold1 a) where
  (==) left right = F1.toNonEmpty left == F1.toNonEmpty right

instance Show a => Show (Unfold1 a) where
  show = show . F1.toNonEmpty







---------------------------------------------------------------------
-- Scan
---------------------------------------------------------------------

mealy :: (x -> a -> x) -> (a -> x) -> (x -> b) -> Scan a b
--mealy h z k = cotabulate $ \(a :| as) -> k (F.foldl' h (z a) as)
mealy h z k = cotabulate $ \u -> k $! runfoldl u h z

purely1 :: (forall x. (x -> a -> x) -> (a -> x) -> (x -> b) -> r) -> Scan a b -> r
--purely1 f s = f (flip (:)) pure (cosieve s . NonEmpty.fromList . P.reverse) 
purely1 f = f snoc pure . cosieve
{-# INLINABLE purely1 #-}

intersperse1 :: a -> Scan a b -> Scan a b
intersperse1 a = purely1 $ \h z k -> mealy (\x b -> (h $! h x a) b) z k
{-# INLINABLE intersperse1 #-}

---------------------------------------------------------------------
-- ScanM
---------------------------------------------------------------------

--data FoldM1 m a b = forall x. FoldM1 (x -> a -> m x) (a -> m x) (x -> m b)

foldM1 :: Monad m => F1.Foldable1 f => ScanM m a b -> f a -> m b
foldM1 (ScanM f z) (F1.toNonEmpty -> (a :| as)) = fmap P.last $ z >>= evalStateT (traverse f $ a:as)

-- TODO: would upgrade to ScanM but need a proof that ScanM ~ FoldM1
foldsM1 :: Monad m => Scan a b -> UnfoldM1 m a -> m b
foldsM1 s (UnfoldM1 u) = purely1 (\h z k -> k <$> u (\x a -> pure $ h a x) (pure . z)) s

---------------------------------------------------------------------
-- Non-empty folds
---------------------------------------------------------------------

-- | Fold all values into a non-empty list.
--
-- @
-- 'fold1' 'list1' = id
-- 'list1' = 'cotabulate' id
-- @
--
list1 :: Scan a (NonEmpty a)
--list1 = cotabulate id
list1 = cotabulate F1.toNonEmpty
{-# INLINABLE list1 #-}

-- | Fold all values into a non-empty list, in reverse order.
--
revList1 :: Scan a (NonEmpty a)
revList1 = mealy (\as a -> nedl a <> as) nedl runNedl
{-# INLINABLE revList1 #-}

--
sconcat :: Semigroup s => (a -> s) -> (s -> b) -> Scan a b
sconcat f = mealy (\x a -> x <> (f a)) f
{-# INLINABLE sconcat #-}

-- | Return the first element in a non-empty container.
--
head1 :: Scan a a
head1 = mealy const id id
{-# INLINABLE head1 #-}

-- | Return the last1 element in a non-empty container.
--
last1 :: Scan a a
last1 = mealy (flip const) id id
{-# INLINABLE last1 #-}

-- | Return the maximum element in a non-empty container.
--
maximum :: Ord a => Scan a a
maximum = mealy max id id
{-# INLINABLE maximum #-}

-- | Return the maximum element with respect to a comparator.
--
maximumBy :: (a -> a -> Ordering) -> Scan a a
maximumBy cmp = mealy max' id id
  where
    max' x y = case cmp x y of
        GT -> x
        _  -> y
{-# INLINABLE maximumBy #-}

-- | Return the minimum element in a non-empty container.
--
minimum :: Ord a => Scan a a
minimum = mealy min id id
{-# INLINABLE minimum #-}

-- | Return the minimum element with respect to a comparator.
--
minimumBy :: (a -> a -> Ordering) -> Scan a a
minimumBy cmp = mealy min' id id
  where
    min' x y = case cmp x y of
        GT -> y
        _  -> x
{-# INLINABLE minimumBy #-}

---------------------------------------------------------------------
-- Orphan Scan instances
---------------------------------------------------------------------


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

--instance Cosieve Scan NonEmpty where
  -- >>> s = cotabulate F.toList :: Scan Int [Int]
  -- >>> cosieve s $ 0 :| [1..3]
  -- [0,1,2,3]
--  cosieve (Scan f z) (a :| as) = P.last $ evalState (traverse f $ a:as) z 

instance Cosieve Scan Unfold1 where
  -- fold1 :: F1.Foldable1 f => Fold1 a b -> f a -> b

  -- >>> cosieve L1.list1 . L1.unfoldr1 $ 0 :| [1..4]
  -- 0 :| [1,2,3,4]
  cosieve (Scan f z) (F1.toNonEmpty -> a :| as) = P.last $ evalState (traverse f $ a:as) z 


instance Corepresentable Scan where
  --type Corep Scan = NonEmpty
  type Corep Scan = Unfold1

  --cotabulate f = Scan go [] where -- TODO optimize
  --  go a = state $ \as -> (f . NonEmpty.fromList $ P.reverse (a:as), a:as) 
  cotabulate f = Scan go mempty where -- TODO a/b test fusion
    go a = state $ \as -> (f $ snoc1 as a, L.snoc as a) 

instance MonadFix (Scan a) where

  mfix = cotabulate . mfix . fmap cosieve

------------------------------------------------------------------------------
-- Nedl 
------------------------------------------------------------------------------

-- | A non-empty difference list.
newtype Nedl a = Nedl { unNedl :: [a] -> L1.NonEmpty a }

instance Semigroup (Nedl a) where
  Nedl f <> Nedl g = Nedl (f . L1.toList . g)

nedl :: a -> Nedl a
nedl a = Nedl (a :|)

runNedl :: Nedl a -> NonEmpty a
runNedl = flip unNedl []

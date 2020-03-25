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
  -- * Free1
    Free1 (..)
  , liftl
  , liftr
  , toFree
  , snoc
  , cons
  , head
  , last
  -- * FreeM1
  -- , FreeM1 (..)
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
uncons :: Free1 a -> (a, Free a) 

scanl :: (b -> a -> b) -> b -> [a] -> [b] 
scanl :: (a -> a -> a) -> [a] -> [a] 
scanr :: (a -> b -> b) -> b -> [a] -> [b] 
scanr :: (a -> a -> a) -> [a] -> [a] 

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
-- Free1
---------------------------------------------------------------------

type Free1 = FreeM1 Identity

pattern Free1 :: (forall x. (a -> x -> x) -> (a -> x) -> x) -> Free1 a
pattern Free1 a <- (retractr -> a) where Free1 a = free1 a

newtype FreeM1 m a = FreeM1 ( forall x. (a -> x -> m x) -> (a -> m x) -> m x )

---------------------------------------------------------------------
-- Introduction
---------------------------------------------------------------------

-- | Obtain an 'Free1' from a left-folding continuation.
--
free1 :: (forall x. (a -> x -> x) -> (a -> x) -> x) -> Free1 a
free1 f = FreeM1 $ \h z -> Identity $ f (\a x -> runIdentity $ h a x) (runIdentity . z)

-- >>> F.foldr (:) [] $ (L1.liftr $ 0 :| [1..3])
-- [0,1,2,3]
liftr :: F1.Foldable1 f => f a -> Free1 a
liftr ((L1.init &&& L1.last) . F1.toNonEmpty -> (as, a)) = Free1 $ \h z -> F.foldr h (z a) as

--Free1 $ \ h z -> F.foldr h (z a) as

liftl :: F1.Foldable1 f => f a -> Free1 a
liftl (F1.toNonEmpty -> a :| as) = snoc1 (L.liftl as) a 

{-
-- | Obtain an 'FreeM' from a 'Data.Foldable.Foldable'.
--
-- >>> F.foldr (:) [] $ liftlM @Identity [0..4]
-- [4,3,2,1,0]
-- >>> F.foldl' (flip (:)) [] $ liftlM @Identity [0..4]
-- [0,1,2,3,4]
--
liftlM :: Monad m => Foldable1 f => f a -> FreeM1 m a
liftlM f = FreeM1 (\ h z -> z >>= flip (F.foldlM $ flip h) f)
{-# INLINE liftlM #-}

-- | Obtain an 'FreeM' from a 'Data.Foldable.Foldable', reversing the order of the elements.
--
-- >>> F.foldr (:) [] $ liftrM @Identity [0..4]
-- [0,1,2,3,4]
-- >>> F.foldl' (flip (:)) [] $ liftrM @Identity [0..4]
-- [4,3,2,1,0]
--
liftrM :: Monad m => Foldable1 f => f a -> FreeM1 m a
liftrM f = FreeM1 (\ h z -> z >>= flip (F.foldrM h) f)
{-# INLINE liftrM #-}
-}
---------------------------------------------------------------------
-- Elimination
---------------------------------------------------------------------

-- | Run an 'Free1'.
--
retractr :: Free1 a -> (forall x . (a -> x -> x) -> (a -> x) -> x)
retractr (FreeM1 u) h z = runIdentity $ u (\a x -> Identity $ h a x) (Identity . z)

retractl :: Free1 a -> (x -> a -> x) -> (a -> x) -> x
retractl (Free1 u) h = u (\a -> flip h a)

-- | Run an 'FreeM1'.
--
retractM :: FreeM1 m a -> (a -> x -> m x) -> (a -> m x) -> m x
retractM (FreeM1 u) h z = u h z

-- | Run an 'FreeM1 IO' inside 'Control.Monad.IO.Unlift.UnliftIO'.
--
retractIO :: MonadUnliftIO m => FreeM1 IO a -> (a -> x -> m x) -> (a -> m x) -> m x
retractIO (FreeM1 u) h z = withRunInIO $ \io -> u (\a x -> io $ h a x) (io . z)

-- | Run an 'Free1' with a continuation function.
--
withFree :: Free1 a -> ((forall x . (a -> x -> x) -> (a -> x) -> x) -> r) -> r
withFree u f = f $ retractr u

-- | Run an 'FreeM1' with a continuation function.
--
withFreeM :: FreeM1 m a -> ((forall x . (a -> x -> m x) -> (a -> m x) -> m x) -> r) -> r
withFreeM u f = f $ retractM u

---------------------------------------------------------------------
-- Basic Interface
---------------------------------------------------------------------

infixr 5 `cons`

-- | Prepend a value to an 'Free1'.
--
-- >>> L1.cons 4 (L1.liftl $ 0 :| [1..3])
-- 4 :| [3,2,1,0]
-- 
cons :: a -> Free1 a -> Free1 a
cons a (Free1 u) = Free1 $ \ h z -> h a (u h z)

infixl 5 `snoc`,`snoc1`

-- | Append a value to an 'Free1'.
--
-- >>> L1.snoc1 (L.liftr [1..3]) 4
-- 1 :| [2,3,4]
-- 
snoc1 :: L.Free a -> a -> Free1 a
snoc1 (L.Free u) a = Free1 $ \ h z -> u h (z a)

-- | Append a value to an 'Free1'.
--
snoc :: Free1 a -> a -> Free1 a
snoc (Free1 u) a = Free1 $ \ h z -> u h (\a1 -> h a1 (z a)) 

-- | Append two 'Free1's.
--
append :: Free1 a -> Free1 a -> Free1 a
append = (<>)

-- | Retrieve the first element of an 'Free1'.
--
head :: Free1 a -> a
head (Free1 u) = u (flip const) id

-- |
--
-- >>> L1.uncons $ L1.liftr (0 :| [1..4])
-- (0,[1,2,3,4])
--
uncons :: Free1 a -> (a, L.Free a) 
uncons = head &&& tail

-- | /O(1)/ Retrieve the last element of an 'Free1'.
--
last :: Free1 a -> a
last (Free1 u) = u const id

-- | /O(1)/ Retrieve the tail of an 'Free1'.
--
tail :: Free1 a -> L.Free a
tail (Free1 u) = L.free $ \ h z -> u h (const z)

-- λ> L1.init (L1.liftl $ 0 :| [1..3])
-- [3,2,1]
init :: Free1 a -> L.Free a
init (Free1 u) = L.free $ \ h z -> u (\ a f -> h a . f) (flip const) z

unsnoc :: Free1 a -> (L.Free a, a) 
unsnoc = init &&& last
---------------------------------------------------------------------
-- Free1 instances
---------------------------------------------------------------------

deriving instance Functor Free1

instance Apply Free1 where
  (<.>) = ap 

instance Applicative Free1 where
  pure a = Free1 (\h z -> h a (z a))
  (<*>) = ap 

instance Alt Free1 where
  (<!>) (Free1 l) (Free1 r) = Free1 (\h z -> r h $ const (l h z))
  {-# INLINE (<!>) #-}

instance Coapply Free1 where 
  coapply = B.bimap liftr liftr . coapply . F1.toNonEmpty

instance Coapplicative Free1 where 
  copure = head

--TODO improve
instance Traversable Free1 where
  -- |
  -- >>> traverse pure $ liftl [1..5]
  -- [1,2,3,4,5]
  traverse f = fmap liftr . traverse f . F1.toNonEmpty

instance Traversable1 Free1 where
  -- |
  -- >>> traverse pure $ liftl [1..5]
  -- [1,2,3,4,5]
  traverse1 f = fmap liftr . traverse1 f . F1.toNonEmpty

instance Monad Free1 where
  return = pure

  (>>=) (Free1 u) f = Free1 $
    \h z -> let h' a x = retractr (f a) h (const x)
                k a = head $ f a -- L1.head $ F1.toNonEmpty (f a)
             in u h' (z . k)

instance Semigroup (Free1 a) where
  (<>) = (<!>)

instance Foldable Free1 where
  --foldMap f u = let (a0, as) = uncons u in L.retractr as (\a x -> f a <> x) (f a0)
  foldMap = F1.foldMap1
  {-# INLINE foldMap #-}
  --foldr h z (Free1 u) = u h $ const z
  --{-# INLINE foldr #-}

instance F1.Foldable1 Free1 where
  foldMap1 f u = let (a0, as) = uncons u in L.retractr as (\a x -> f a <> x) (f a0)

instance Eq a => Eq (Free1 a) where
  (==) left right = F1.toNonEmpty left == F1.toNonEmpty right

instance Show a => Show (Free1 a) where
  show = show . F1.toNonEmpty







---------------------------------------------------------------------
-- Scan
---------------------------------------------------------------------

mealy :: (x -> a -> x) -> (a -> x) -> (x -> b) -> Scan a b
--mealy h z k = cotabulate $ \(a :| as) -> k (F.foldl' h (z a) as)
mealy h z k = cotabulate $ \u -> k $! retractl u h z

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
foldsM1 :: Monad m => Scan a b -> FreeM1 m a -> m b
foldsM1 s (FreeM1 u) = purely1 (\h z k -> k <$> u (\x a -> pure $ h a x) (pure . z)) s

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

instance Cosieve Scan Free1 where
  -- fold1 :: F1.Foldable1 f => Fold1 a b -> f a -> b

  -- >>> cosieve L1.list1 . L1.liftr $ 0 :| [1..4]
  -- 0 :| [1,2,3,4]
  cosieve (Scan f z) (F1.toNonEmpty -> a :| as) = P.last $ evalState (traverse f $ a:as) z 


instance Corepresentable Scan where
  --type Corep Scan = NonEmpty
  type Corep Scan = Free1

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

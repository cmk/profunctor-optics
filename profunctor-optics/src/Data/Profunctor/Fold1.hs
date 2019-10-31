{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Data.Profunctor.Fold1 where

import Control.Applicative
import Control.Arrow
import Control.Category
import Control.Monad.Fix
import Control.Monad.Reader.Class
import Control.Monad.Zip
import Data.Distributive
import Data.Functor.Apply
import Data.List.NonEmpty as NonEmpty
import Data.Profunctor.Closed
import Data.Profunctor
import Data.Profunctor.Rep as Profunctor
import Data.Profunctor.Sieve
import Data.Profunctor.Unsafe
import Data.Semigroupoid
import Prelude hiding (id,(.))
import Unsafe.Coerce

import Data.Typeable
import Data.Data

-- | A Mealy Machine
data Fold1 a b = forall s. Fold1 (s -> a -> s) (a -> s) (s -> b)

mealy :: (s -> a -> (b, s)) -> s -> a -> Fold1 a b
mealy f s a = Fold1 (\x y -> snd $ f x y) (snd . f s) (fst . flip f a)
{-# INLINE mealy #-}

-- | Strict Pair
data Pair a b = Pair !a !b deriving (Eq,Ord,Show,Read,Typeable,Data)

instance (Semigroup a, Semigroup b) => Semigroup (Pair a b) where
  Pair a b <> Pair c d = Pair (a <> c) (b <> d)
  {-# INLINE (<>) #-}

instance (Monoid a, Monoid b) => Monoid (Pair a b) where
  mempty = Pair mempty mempty
  {-# INLINE mempty #-}

{-

instance Scan Fold1 where
  run1 a (Fold1 k _ z) = k (z a)
  prefix1 a (Fold1 h z k) = Fold1 k h (h (z a))
  postfix1 (Fold1 h z k) a = Fold1 (\c -> k (h c a)) h z
  interspersing a (Fold1 h z k) = Fold1 k (\x b -> h (h x a) b) z
  {-# INLINE run1 #-}
  {-# INLINE prefix1 #-}
  {-# INLINE postfix1 #-}
  {-# INLINE interspersing #-}
-}
walk :: SnocList1 a -> Fold1 a b -> b
walk xs0 (Fold1 h z k) = k (go xs0) where
  go (First a) = z a
  go (Snoc1 as a) = h (go as) a
{-# INLINE walk #-}

data SnocList1 a = Snoc1 (SnocList1 a) a | First a
  deriving (Eq,Ord,Show,Read,Typeable,Data)

instance Functor SnocList1 where
  fmap f (Snoc1 xs x) = Snoc1 (fmap f xs) (f x)
  fmap f (First a) = First (f a)
  {-# INLINABLE fmap #-}

instance Foldable SnocList1 where
  foldl f z m0 = go m0 where
    go (Snoc1 xs x) = f (go xs) x
    go (First a) = f z a
  {-# INLINE foldl #-}
  foldl1 f m0 = go m0 where
    go (Snoc1 xs x) = f (go xs) x
    go (First a) = a
  {-# INLINE foldl1 #-}
  foldMap f (Snoc1 xs x) = foldMap f xs `mappend` f x
  foldMap f (First a) = f a
  {-# INLINABLE foldMap #-}

instance Traversable SnocList1 where
  traverse f (Snoc1 xs x) = Snoc1 <$> traverse f xs <*> f x
  traverse f (First a) = First <$> f a
  {-# INLINABLE traverse #-}

instance Functor (Fold1 a) where
  fmap f (Fold1 h z k) = Fold1 h z (f . k)
  {-# INLINE fmap #-}
  b <$ _ = pure b
  {-# INLINE (<$) #-}

instance Apply (Fold1 a) where
  (<.>) = (<*>)
  {-# INLINE (<.>) #-}
  (<.) m = \_ -> m
  {-# INLINE (<.) #-}
  _ .> m = m
  {-# INLINE (.>) #-}

instance Applicative (Fold1 a) where
  pure x = Fold1 (\() _ -> ()) (\_ -> ()) (\() -> x)
  {-# INLINE pure #-}
  Fold1 hf zf kf <*> Fold1 ha za ka = Fold1
    (\(Pair x y) a -> Pair (hf x a) (ha y a))
    (\a -> Pair (zf a) (za a))
    (\(Pair x y) -> kf x (ka y))
  (<*) m = \ _ -> m
  {-# INLINE (<*) #-}
  _ *> m = m
  {-# INLINE (*>) #-}

instance Monad (Fold1 a) where
  return = pure
  {-# INLINE return #-}
  m >>= f = Fold1 Snoc1 First (\xs a -> walk xs (f a)) <*> m
  {-# INLINE (>>=) #-}
  (>>) = (*>)
  {-# INLINE (>>) #-}

instance MonadZip (Fold1 a) where
  mzipWith = liftA2
  {-# INLINE mzipWith #-}

instance Semigroupoid Fold1 where
  o = (.)
  {-# INLINE o #-}

instance Category Fold1 where
  id = arr id
  {-# INLINE id #-}
  Fold1 h z k . Fold1 h' z' k' = Fold1 h'' z'' (\(Pair b _) -> k b) where
    z'' a = Pair (z (k' b)) b where b = z' a
    h'' (Pair c d) a = Pair (h c (k' d')) d' where d' = h' d a
  {-# INLINE (.) #-}

instance Arrow Fold1 where
  arr h = Fold1 (\_ a -> a) id h
  {-# INLINE arr #-}
  first (Fold1 h z k) = Fold1 h' (first z) (first k) where
    h' (a,_) (c,b) = (h a c, b)
  {-# INLINE first #-}
  second (Fold1 h z k) = Fold1 h' (second z) (second k) where
    h' (_,b) (a,c) = (a, h b c)
  {-# INLINE second #-}
  Fold1 h z k *** Fold1 h' z' k' = Fold1 h'' (z *** z') (k *** k') where
    h'' (a,b) (c,d) = (h a c, h' b d)
  {-# INLINE (***) #-}
  Fold1 h z k &&& Fold1 h' z' k' = Fold1 h'' (z &&& z') (k *** k') where
    h'' (c,d) a = (h c a, h' d a)
  {-# INLINE (&&&) #-}

instance Profunctor Fold1 where
  dimap f g (Fold1 h z k) = Fold1 (\a -> h a . f) (z . f) (g . k)
  {-# INLINE dimap #-}
  lmap f (Fold1 h z k) = Fold1 (\a -> h a . f) (z . f) k
  {-# INLINE lmap #-}
  rmap g (Fold1 h z k) = Fold1 h z (g . k)
  {-# INLINE rmap #-}
  ( #. ) _ = unsafeCoerce
  {-# INLINE (#.) #-}
  x .# _ = unsafeCoerce x
  {-# INLINE (.#) #-}

instance Strong Fold1 where
  first' = first
  {-# INLINE first' #-}
  second' = second
  {-# INLINE second' #-}

instance Choice Fold1 where
  left' (Fold1 h z k) = Fold1 step (left' `id` z) (left' `id` k) where
    step (Left x) (Left y) = Left (h x y)
    step (Right c) _ = Right c
    step _ (Right c) = Right c
  {-# INLINE left' #-}

  right' (Fold1 h z k) = Fold1 step (right' `id` z) (right' `id` k) where
    step (Right x) (Right y) = Right (h x y)
    step (Left c) _ = Left c
    step _ (Left c) = Left c
  {-# INLINE right' #-}

instance ArrowChoice Fold1 where
  left (Fold1 h z k) = Fold1 step (left' `id` z) (left' `id` k) where
    step (Left x) (Left y) = Left (h x y)
    step (Right c) _ = Right c
    step _ (Right c) = Right c
  {-# INLINE left #-}

  right (Fold1 h z k) = Fold1 step (right' `id` z) (right' `id` k) where
    step (Right x) (Right y) = Right (h x y)
    step (Left c) _ = Left c
    step _ (Left c) = Left c
  {-# INLINE right #-}

instance Cosieve Fold1 NonEmpty where
  cosieve (Fold1 h z k) (a :| as) = k (foldl h (z a) as)

instance Costrong Fold1 where
  unfirst = unfirstCorep
  unsecond = unsecondCorep

instance Profunctor.Corepresentable Fold1 where
  type Corep Fold1 = NonEmpty
  cotabulate f = Fold1 (flip (:)) pure (f . NonEmpty.fromList . Prelude.reverse)
  {-# INLINE cotabulate #-}

{-
instance Distributive (Fold1 a) where
  --distribute = distributeRep
  distribute x = Fold1 (\fm a -> fmap (prefix1 a) fm) x (fmap extract)
-}

instance Closed Fold1 where
  closed (Fold1 h z k) = Fold1 (liftA2 h) (fmap z) (\f x -> k (f x))

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
import Data.Functor.Rep as Functor
import Data.Profunctor.Closed
import Data.Profunctor
import Data.Profunctor.Rep as Profunctor
import Data.Profunctor.Sieve
import Data.Profunctor.Unsafe
import Prelude hiding (id,(.))
import Unsafe.Coerce
import Data.Typeable
import Data.Data
import Data.Strict (Pair(..))

-- | A Mealy Machine
data Fold1 a b = forall s. Fold1 (s -> a -> s) (a -> s) (s -> b)

mealy :: (s -> a -> (b, s)) -> s -> a -> Fold1 a b
mealy f s a = Fold1 (\x y -> snd $ f x y) (snd . f s) (fst . flip f a)
{-# INLINE mealy #-}

run1 :: a -> Fold1 a p -> p
run1 a (Fold1 _ z k) = k (z a)
{-# INLINE run1 #-}

prefix1 :: a -> Fold1 a b -> Fold1 a b
prefix1 a (Fold1 h z k) = Fold1 h (h $! z a) k
{-# INLINE prefix1 #-}

postfix1 :: Fold1 a b -> a -> Fold1 a b
postfix1 (Fold1 h z k) a = Fold1 h z (\c -> k $! h c a)
{-# INLINE postfix1 #-}

intersperse :: a -> Fold1 a b -> Fold1 a b
intersperse a (Fold1 h z k) = Fold1 (\x b -> (h $! h x a) b) z k
{-# INLINE intersperse #-}

instance Functor (Fold1 a) where
  fmap f (Fold1 h z k) = Fold1 h z (f . k)
  {-# INLINE fmap #-}

  b <$ _ = pure b
  {-# INLINE (<$) #-}

instance Distributive (Fold1 a) where
  distribute = distributeRep

instance Functor.Representable (Fold1 a) where
  type Rep (Fold1 a) = NonEmpty a

  tabulate = cotabulate

  index = cosieve

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
    (\(x :!: y) a -> (hf x a) :!: (ha y a))
    (\a -> (zf a) :!: (za a))
    (\(x :!: y) -> kf x (ka y))

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

instance Category Fold1 where
  id = arr id
  {-# INLINE id #-}

  Fold1 h z k . Fold1 h' z' k' = Fold1 h'' z'' (\(b :!: _) -> k b) where
    z'' a = (z (k' b)) :!: b where b = z' a
    h'' (c :!: d) a = (h c (k' d')) :!: d' where d' = h' d a
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

instance Closed Fold1 where
  closed (Fold1 h z k) = Fold1 (liftA2 h) (fmap z) (\f x -> k (f x))

instance MonadReader (NonEmpty a) (Fold1 a) where
  ask = askRep

  local = localRep

instance MonadFix (Fold1 a) where
  mfix = mfixRep

data SnocList1 a = Snoc1 (SnocList1 a) a | First a
  deriving (Eq,Ord,Show,Read,Typeable,Data)

walk :: SnocList1 a -> Fold1 a b -> b
walk xs0 (Fold1 h z k) = k (go xs0) where
  go (First a) = z a
  go (Snoc1 as a) = h (go as) a
{-# INLINE walk #-}

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

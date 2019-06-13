module Data.Valid where

import Data.Semiring
import Data.Dioid

import Control.Applicative
import Data.Bifoldable(Bifoldable(bifoldr))
import Data.Bifunctor(Bifunctor(bimap))
import Data.Bitraversable(Bitraversable(bitraverse))
import Data.Foldable (Foldable(foldr))
import Data.Functor.Alt (Alt((<!>)))
import Data.Functor.Apply (Apply ((<.>)))
import Data.Monoid (Monoid(mappend, mempty))
import Data.Semigroup (Semigroup((<>)))
import Data.Traversable (Traversable(traverse))
import Prelude hiding (foldr)

data Valid e a = Invalid e | Valid a deriving (Eq, Ord, Show)


validToEither :: Valid e a -> Either e a
validToEither x = case x of
  Invalid e -> Left e
  Valid a -> Right a
{-# INLINE validToEither #-}

eitherToValid :: Either e a -> Valid e a
eitherToValid x = case x of
  Left e -> Invalid e
  Right a -> Valid a
{-# INLINE eitherToValid #-}

vap :: Semigroup m => Either m (a -> b) -> Either m a -> Either m b
vap (Left m) b = Left $ case b of
  Left n  -> m <> n
  Right{} -> m
vap Right{} (Left n) = Left n
vap (Right f) (Right a) = Right (f a)
{-# INLINE vap #-}

apm :: Monoid m => Valid m (a -> b) -> Valid m a -> Valid m b
apm (Invalid m) b = Invalid $ m `mappend` case b of
  Invalid n  -> n
  Valid{} -> mempty
apm Valid{} (Invalid n) = Invalid n
apm (Valid f) (Valid a) = Valid (f a)
{-# INLINE apm #-}

-- lazier version of vap that can leak less, but which requires a Monoid
vapm :: Monoid m => Either m (a -> b) -> Either m a -> Either m b
vapm (Left m) b = Left $ m `mappend` case b of
  Left n  -> n
  Right{} -> mempty
vapm Right{} (Left n) = Left n
vapm (Right f) (Right a) = Right (f a)
{-# INLINE vapm #-}

ealt :: Valid e a -> Valid e a -> Valid e a
ealt Invalid{} r = r
ealt (Valid a) _ = Valid a
{-# INLINE ealt #-}


instance Semigroup e => Semigroup (Valid e a) where

  x@Valid{} <> _           = x

  _ <> x@Valid{}           = x

  Invalid e1 <> Invalid e2 = Invalid (e1 <> e2)


instance Monoid e => Monoid (Valid e a) where

  mempty = Invalid mempty


{-
instance (Semiring e, Semiring a) => Semiring (Valid e a) where

  Valid a >< Valid b     = Valid $ a >< b

  Valid _ >< Invalid e   = Invalid e

  Invalid e >< Invalid f = Invalid $ e >< f

  Invalid e >< _         = Invalid e


  --fromNatural = fromNaturalDef $ Valid one


instance (Dioid e, Semiring a, Eq a) => Dioid (Valid e a) where

  Valid a `ord` Valid b     = a == b
  Valid _ `ord` _           = False
  
  Invalid e `ord` Invalid f = ord e f
  Invalid _ `ord` _         = True
-}


instance Functor (Valid e) where

   fmap _ (Invalid e) = Invalid e

   fmap f (Valid a) = Valid (f a)


instance Semiring e => Apply (Valid e) where

  Invalid e1 <.> Invalid e2 = Invalid $ e1 >< e2

  Invalid e <.> Valid _ = Invalid e

  Valid _ <.> Invalid e = Invalid e

  Valid f  <.> Valid x  = Valid (f x)


instance Semiring e => Applicative (Valid e) where

  pure = Valid

  (<*>) = (<.>)


instance Semigroup e => Alt (Valid e) where

  (<!>) = (<>)


instance (Monoid e, Semiring e) => Alternative (Valid e) where

  empty = Invalid mempty

  (<|>) = (<>)


instance Foldable (Valid e) where
  foldr f x (Valid a) = f a x
  foldr _ x (Invalid _) = x

instance Traversable (Valid e) where
  traverse f (Valid a) = Valid <$> f a
  traverse _ (Invalid e) = pure (Invalid e)

instance Bifunctor Valid where
  bimap f _ (Invalid e) = Invalid (f e)
  bimap _ g (Valid a) = Valid (g a)

instance Bifoldable Valid where
  bifoldr _ g x (Valid a) = g a x
  bifoldr f _ x (Invalid e) = f e x

instance Bitraversable Valid where
  bitraverse _ g (Valid a) = Valid <$> g a
  bitraverse f _ (Invalid e) = Invalid <$> f e



module Data.Valid where

import Data.Bifoldable (Bifoldable(bifoldr))
import Data.Bifunctor (Bifunctor(bimap))
import Data.Bitraversable( Bitraversable(bitraverse))
import Data.Dioid
import Data.Foldable (Foldable(foldr))
import Data.Functor.Alt (Alt((<!>)))
import Data.Functor.Apply (Apply ((<.>)))
import Data.Semiring
import Data.Traversable (Traversable(traverse))

import P

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


instance Semigroup e => Semigroup (Valid e a) where
  x@Valid{} <> _           = x

  _ <> x@Valid{}           = x

  Invalid e1 <> Invalid e2 = Invalid (e1 <> e2)


instance Monoid e => Monoid (Valid e a) where
  mempty = Invalid mempty


instance (Monoid e, Monoid a, Semiring e) => Semiring (Valid e a) where
  Valid a >< Valid b     = Valid $ a <> b

  Invalid e >< Invalid f = Invalid $ e >< f

  x@Invalid{} >< _       = x

  _ >< x@Invalid{}       = x

  fromBoolean = fromBooleanDef $ Valid mempty


instance (Dioid e, Eq a, Monoid a, Monoid e) => Dioid (Valid e a) where
  Valid a `ord` Valid b     = a == b
  Valid{} `ord` _           = False
  
  Invalid e `ord` Invalid f = e `ord` f
  Invalid{} `ord` _         = True


instance Functor (Valid e) where
   fmap _ (Invalid e) = Invalid e

   fmap f (Valid a) = Valid (f a)


instance Semiring e => Apply (Valid e) where
  (<.>) = vap


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


vap :: Semiring m => Valid m (a -> b) -> Valid m a -> Valid m b
vap (Invalid m) b = Invalid $ case b of
  Invalid n -> m >< n
  Valid{}   -> m
vap Valid{} (Invalid n) = Invalid n
vap (Valid f) (Valid a) = Valid (f a)
{-# INLINE vap #-}


-- A lazier version of 'vap' that can leak less, but which requires a unital semiring.
vapm :: (Monoid m, Semiring m) => Valid m (a -> b) -> Valid m a -> Valid m b
vapm (Invalid m) b = Invalid $ m >< case b of
  Invalid n  -> n
  Valid{}    -> one
vapm Valid{} (Invalid n) = Invalid n
vapm (Valid f) (Valid a) = Valid (f a)
{-# INLINE vapm #-}

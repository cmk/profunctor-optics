
module Data.Ring where

import Data.Semigroup
import Data.Monoid
import Data.Semiring
import Data.Hemiring

class Hemiring r => Ring r where 
  
  neg :: r -> r



-- | Provide the correct Monoid, Hemiring, and Unital instances for an arbitrary Num. Used with GHC 8.6+'s DerivingVia extension.
newtype WrappedNum a = WrappedNum { unwrappedNum :: a } deriving (Eq, Show, Num, Ord, Functor)
{-
  deriving
    ( Eq
    , Foldable
    , Fractional
    , Functor
    , Generic
    , Generic1
    , Num
    , Ord
    , Real
    , RealFrac
    , Show
    , Storable
    , Traversable
    , Typeable
    )
-}

instance Num a => Semigroup (WrappedNum a) where

  (<>) = (+)


instance Num a => Monoid (WrappedNum a) where

  mempty = 0


instance Num a => Semiring (WrappedNum a) where

  (><) = (*)
  {-# INLINE (><) #-}


instance Num a => Hemiring (WrappedNum a) where

  fromNatural = fromNaturalDef mempty 1


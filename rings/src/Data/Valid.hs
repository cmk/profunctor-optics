module Data.Valid where


--import Data.Semigroup
import Data.Semiring
import Data.Hemiring
import Data.Dioid

data Valid e a = Invalid e | Valid a deriving (Show, Eq) --TODO more instances & move to module


instance (Semigroup e, Semigroup a) => Semigroup (Valid e a) where

  Valid a <> Valid b     = Valid $ a <> b

  Valid _ <> Invalid e   = Invalid e

  Invalid e <> Invalid f = Invalid $ e <> f

  Invalid e <> _         = Invalid e 


instance (Semigroup e, Monoid a) => Monoid (Valid e a) where

  mempty = Valid mempty


instance (Semiring e, Semiring a) => Semiring (Valid e a) where

  Valid a >< Valid b     = Valid $ a >< b

  Valid _ >< Invalid e   = Invalid e

  Invalid e >< Invalid f = Invalid $ e >< f

  Invalid e >< _         = Invalid e


instance (Semiring e, Hemiring a) => Hemiring (Valid e a) where

  fromNatural = fromNaturalDef (Valid zero) (Valid one)


instance (Dioid e, Dioid a) => Dioid (Valid e a) where

  Valid a `ord` Valid b     = ord a b
  Valid _ `ord` _           = True
  
  Invalid e `ord` Invalid f = ord e f
  Invalid _ `ord` _         = False


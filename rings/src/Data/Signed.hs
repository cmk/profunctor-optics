module Data.Signed where


--import Data.Semigroup
import Data.Semiring
import Data.Hemiring
import Data.Dioid



data Signed a = Zero | Negative a | Positive a | Indeterminate a deriving (Show, Eq)

instance Semigroup a => Semigroup (Signed a) where

  Positive a <> Positive b          = Positive $ a <> b
  Positive a <> Negative b          = Indeterminate $ a <> b
  Positive a <> Zero                = Positive a
  Positive a <> Indeterminate e     = Indeterminate $ a <> e

  Negative a <> Negative b          = Negative $ a <> b
  Negative a <> Positive b          = Indeterminate $ a <> b
  Negative a <> Zero                = Negative a
  Negative a <> Indeterminate e     = Indeterminate $ a <> e

  Zero <> a                       = a

  Indeterminate a <> Positive b          = Indeterminate $ a <> b
  Indeterminate a <> Negative b          = Indeterminate $ a <> b
  Indeterminate a <> Zero                = Indeterminate a
  Indeterminate a <> Indeterminate e     = Indeterminate $ a <> e

instance Semigroup a => Monoid (Signed a) where

  mempty = Zero

{-

instance Monoid a => Semiring (Signed a) where

  zero = mempty

  one = Positive mempty

  Positive >< a = a

  Negative >< Positive            = Negative
  Negative >< Negative            = Positive
  Negative >< Zero                = Zero
  Negative >< Indeterminate       = Indeterminate

  Zero >< _                       = Zero
  Indeterminate >< _              = Indeterminate

  
instance Dioid Signed where

  Positive `ord` Positive         = True
  Positive `ord` Indeterminate    = True
  Positive `ord` _                = False

  Negative `ord` Negative         = True
  Negative `ord` Indeterminate    = True
  Negative `ord` _                = False

  ord Zero       _                = True

  ord Indeterminate Indeterminate = True
  ord Indeterminate _             = False

-}



{- 

+ can be regarded as representing [0, +∞], – as representing [−∞, 0], ? as representing [−∞, +∞], and 0 as representing the set {0}.

? ≥+≥ 0 and ? ≥−≥ 0
instance Ord Sign where
  
  compare 

data Sign = Positive | Negative | Zero | Indeterminate deriving (Show, Eq)

instance Semigroup Sign where

  Positive <> Positive            = Positive
  Positive <> Negative            = Indeterminate
  Positive <> Zero                = Positive
  Positive <> Indeterminate       = Indeterminate

  Negative <> Positive            = Indeterminate
  Negative <> Negative            = Negative
  Negative <> Zero                = Negative
  Negative <> Indeterminate       = Indeterminate

  Zero <> a                       = a

  Indeterminate <> _              = Indeterminate


instance Monoid Sign where

  mempty = Zero

instance Semiring Sign where

  zero = mempty

  one = Positive

  Positive >< a = a

  Negative >< Positive            = Negative
  Negative >< Negative            = Positive
  Negative >< Zero                = Zero
  Negative >< Indeterminate       = Indeterminate

  Zero >< _                       = Zero
  Indeterminate >< _              = Indeterminate

  
instance Dioid Sign where

  Positive `ord` Positive         = True
  Positive `ord` Indeterminate    = True
  Positive `ord` _                = False

  Negative `ord` Negative         = True
  Negative `ord` Indeterminate    = True
  Negative `ord` _                = False

  ord Zero       _                = True

  ord Indeterminate Indeterminate = True
  ord Indeterminate _             = False


-}



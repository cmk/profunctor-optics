module Data.Signed where

import Control.Applicative
import Data.Semiring
import Data.Dioid


 

-- | In the case where @a@ is real or integer-valued: 
--   * 'Positive' can be regarded as representing [0, +∞], 
--   * 'Negative' as representing [−∞, 0], 
--   * 'Indeterminate' as representing [−∞, +∞], and 
--   * 'Zero' as representing the set {0}.

data Signed a = Zero | Negative a | Positive a | Indeterminate a deriving (Show, Eq)



instance Semigroup a => Semigroup (Signed a) where

  Positive a <> Positive b           = Positive $ a <> b
  Positive a <> Negative b           = Indeterminate $ a <> b
  Positive a <> Zero                 = Positive a
  Positive a <> Indeterminate e      = Indeterminate $ a <> e

  Negative a <> Negative b           = Negative $ a <> b
  Negative a <> Positive b           = Indeterminate $ a <> b
  Negative a <> Zero                 = Negative a
  Negative a <> Indeterminate e      = Indeterminate $ a <> e

  Zero <> a                          = a

  Indeterminate a <> Positive b      = Indeterminate $ a <> b
  Indeterminate a <> Negative b      = Indeterminate $ a <> b
  Indeterminate a <> Zero            = Indeterminate a
  Indeterminate a <> Indeterminate e = Indeterminate $ a <> e


instance Semigroup a => Monoid (Signed a) where

  mempty = Zero

{-
instance Semigroup a => Alternative Signed where
  empty = mempty
  (<|>) = (<>)

-}
instance (Monoid a, Semiring a) => Semiring (Signed a) where

  Positive a >< Positive b           = Positive $ a >< b
  Positive a >< Negative b           = Negative $ a >< b
  Positive _ >< Zero                 = Zero
  Positive a >< Indeterminate e      = Indeterminate $ a >< e

  Negative a >< Positive b           = Negative $ a >< b
  Negative a >< Negative b           = Positive $ a >< b
  Negative _ >< Zero                 = Zero
  Negative a >< Indeterminate e      = Indeterminate $ a >< e

  Zero >< _                          = Zero
 
  Indeterminate a >< Positive b      = Indeterminate $ a >< b
  Indeterminate a >< Negative b      = Indeterminate $ a >< b
  Indeterminate a >< Zero            = Zero
  Indeterminate a >< Indeterminate e = Indeterminate $ a >< e


  fromNatural = fromNaturalDef $ Positive mempty

{-
instance Semiring a => Apply (These a) where
    This  a   <.> _         = This a
    That    _ <.> This  b   = This b
    That    f <.> That    x = That (f x)
    That    f <.> These b x = These b (f x)
    These a _ <.> This  b   = This (a <> b)
    These a f <.> That    x = These a (f x)
    These a f <.> These b x = These (a <> b) (f x)

instance Semiring a => Applicative Signed where
  
  pure = Positive
  (<*>) = (<.>)
-}


-- | This instance superimposes a 4-part ordering on top of the 
-- ordering of @a@.
-- 
instance (Monoid a, Dioid a) => Dioid (Signed a) where

  Positive a `ord` Positive b           = ord a b
  Positive a `ord` Indeterminate b      = ord a b
  Positive _ `ord` _                    = False

  Negative a `ord` Negative b           = ord a b
  Negative a `ord` Indeterminate b      = ord a b
  Negative _ `ord` _                    = True

  Zero `ord` Positive _                 = True
  Zero `ord` Negative _                 = False
  Zero `ord` Zero                       = True
  Zero `ord` Indeterminate a            = ord zero a

  Indeterminate a `ord` Positive b      = ord a b
  Indeterminate a `ord` Negative b      = ord a b
  Indeterminate a `ord` Zero            = ord a zero
  Indeterminate a `ord` Indeterminate b = ord a b




{- 

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
  Positive `ord` Indeterminate    = True -- bad instance
  Positive `ord` _                = False

  Negative `ord` Negative         = True
  Negative `ord` Indeterminate    = True -- bad instance
  Negative `ord` _                = False

  ord Zero       _                = True

  ord Indeterminate Indeterminate = True -- bad instance
  ord Indeterminate _             = False


-}



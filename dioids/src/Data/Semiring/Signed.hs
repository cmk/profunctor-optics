module Data.Semiring.Signed where

import Control.Applicative
import Data.Semiring
import Data.Dioid


 




-- | 'Sign' is isomorphic to '(Any,Any)' as a monoid, but has a distinct ordering.
--
-- The following order relations hold: 
-- @ 'Indeterminate' >= 'Positive' >= 'Zero'@ and
-- @ 'Indeterminate' >= 'Negative' >= 'Zero'@ 
--
-- Note that 'Positive' and 'Negative' are not comparable as they are in '(Any,Any)':
--
-- @ ('Any' True, 'Any' False) >= ('Any' False, 'Any' True)@
--
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

  Positive >< a = a

  Negative >< Positive            = Negative
  Negative >< Negative            = Positive
  Negative >< Zero                = Zero
  Negative >< Indeterminate       = Indeterminate

  Zero >< _                       = Zero

  Indeterminate >< Zero           = Zero
  Indeterminate >< _              = Indeterminate

  fromBoolean = fromBooleanDef Positive
 

instance Dioid Sign where

  Positive `ord` Positive         = True
  Positive `ord` Negative         = False
  Positive `ord` Zero             = False
  Positive `ord` Indeterminate    = True

  Negative `ord` Positive         = False
  Negative `ord` Negative         = True
  Negative `ord` Zero             = False
  Negative `ord` Indeterminate    = True


  ord Zero       _                = True

  ord Indeterminate Indeterminate = True
  ord Indeterminate _             = False



-- | In the case where @a@ is some kind of positive-real (e.g. 'Natural'):
--   * 'Positive' can be regarded as representing [0, +∞], 
--   * 'Negative' as representing [−∞, 0], 
--   * 'Indeterminate' as representing [−∞, +∞], and 
--   * 'Zero' as representing the set {0}.

data Signed a = Signed Sign a deriving (Show, Eq)

instance Semigroup a => Semigroup (Signed a) where

  Signed s a <> Signed t b = Signed (s<>t) (a<>b)

instance Monoid a => Monoid (Signed a) where

  mempty = Signed mempty mempty

instance (Monoid a, Semiring a) => Semiring (Signed a) where

  Signed s a >< Signed t b = Signed (s><t) (a><b) 

--instance Dioid a => Dioid (Signed a) where Signed s a `ord` Signed t b = 
{-
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


  fromBoolean = fromBooleanDef $ Positive mempty

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
-- See Gondran and Minoux ex 6.8.2.
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

-}


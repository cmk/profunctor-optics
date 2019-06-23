
module Data.Ring where

import Data.Semigroup
import Data.Monoid
import Data.Semiring

import P


class Semiring r => Ring r where 
  
  neg :: r -> r

  fromInteger :: Integer -> r
  --fromInteger i = if i >= 0 then 

{-
--sgn :: a -> Signed a
--sgn :: a -> Sign
--abs :: a -> a

instance Ring b => Ring (a -> b) where
  neg f x = neg (f x)
  {-# INLINE neg #-}


--instance (Semigroup a, Semigroup b) => Semigroup (a, b)

--instance Semigroup Ordering

instance Ring () where
  neg _ = ()
  {-# INLINE neg #-}
-}
{-
instance Ring a => Ring (Complex a) where
  neg (x :+ y) = neg x :+ neg y
  {-# INLINE negate #-}

instance Ring a => Ring (Const a b) where
  neg (Const x) = Const (neg x)
  {-# INLINE negate #-}

instance Ring a => Ring (Dual a) where
  neg (Dual x) = Dual (neg x)
  {-# INLINE neg #-}

-}






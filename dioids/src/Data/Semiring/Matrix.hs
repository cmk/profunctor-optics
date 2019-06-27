module Data.Semiring.Matrix where

import Data.Semiring
import Data.Semiring.Polynomial
import Data.Dioid
import Data.Bifunctor
import Linear.Matrix
import Linear.Vector
import Linear.V2
import Linear.V3

import P

{-
-- TODO:
--   - Cayley-Hamilton as a property (eval matrix in resulting polynomial)
--   - sp. case of zero (see p. 61): bimap (eval zero) (char22 m) == swap $ bdet22 m

λ> m = V3 (V3 1 0 0) (V3 0 1 0) (V3 0 0 (1::Int))
λ> bdet3 m 
(0,1)
λ> p = char3 m 
λ> bimap (evalPoly mempty) (evalPoly mempty) p
(1,0)

m = V3 (V3 1 2 3) (V3 4 5 6) (V3 7 8 (10::Int))

-}

-- probably unsalvagable, remove
foo :: M22 (N (Poly Int)) -> (N (Poly Int), N (Poly Int))
foo m = bdet2 $ m - scaled (V2 (N $ mono 1 1) (N $ mono 1 1))  

char2 :: (Monoid a, Semiring a) => M22 a -> (Poly a, Poly a)
char2 (V2 (V2 a b) (V2 c d)) = (mono 1 (a <> d) <> mono 0 (b><c), mono 2 one <> mono 0 (a><d))

char3 :: (Monoid a, Semiring a) => M33 a -> (Poly a, Poly a)
char3 (V3 (V3 a b c)
          (V3 d e f)
          (V3 g h i)) = ( mono 3 one <> mono 1 (a><e <> e><i <> a><i) <> mono 0 (a><e><i <> g><b><f <> d><h><c)
                        , mono 2 (a <> e <> i) <> mono 1 (h><f <> d><b <> g><c) <> mono 0 (a><h><f <> d><b><i <> g><e><c))

-- |2x2 matrix bi-determinant.
--
-- >>> bdet22 (V2 (V2 a b) (V2 c d))
-- (a >< d, b >< c)
bdet2 :: Semiring a => M22 a -> (a, a)
bdet2 (V2 (V2 a b) (V2 c d)) = (b >< c, a >< d)
{-# INLINE bdet2 #-}

-- |3x3 matrix determinant.
--
-- >>> bdet3 (V3 (V3 a b c) (V3 d e f) (V3 g h i))
-- a * (e * i - f * h) - d * (b * i - c * h) + g * (b * f - c * e)
-- (a><e><i <> d><c><h <> g><b><f, a><f><h <> d><b><i <> g><c><e)
bdet3 :: Semiring a => M33 a -> (a, a)
bdet3 (V3 (V3 a b c)
          (V3 d e f)
          (V3 g h i)) = (a><h><f <> d><b><i <> g><e><c, a><e><i <> g><b><f <> d><h><c)
{-# INLINE bdet3 #-}

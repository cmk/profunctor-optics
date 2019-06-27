module Data.Semiring.Polynomial where


import Data.Semiring
import Data.Dioid
import Data.List (zipWith)
import Data.Typeable (Typeable)
import Data.Validity
import Data.Validity.Map
import Data.GenValidity
import Data.GenValidity.Map
import Data.Functor.Classes
import GHC.Generics (Generic, Generic1)

import P
import Orphans ()
import qualified Data.Map as Map


-- | Univariate polynomials over an arbitrary semiring.
--
-- Constants are always at the head of the list, and the
-- encoding proceeds 'to the right', for example @3 + 4x^2@  
-- is represented as the list @[3, 0, 4]@.
--
-- Due to the laziness of the underlying list type, we may
-- encode infinite polynomials (i.e. power series) and thus
-- implement 'Closed' as well as 'Semiring'. 
--
-- For a more efficient implementation of (finite) univariate
-- polynomials, use 'Poly'.
newtype Polynomial a = Polynomial { runPolynomial :: [a] }
  deriving (Eq, Ord, Show, Functor, Generic, GenUnchecked, GenValid, Typeable, Validity)
  --deriving Num via (N (Polynomial a))

instance Semigroup a => Semigroup (Polynomial a) where
  Polynomial [] <> y = y
  y <> Polynomial [] = y
  Polynomial (a:as) <> Polynomial (b:bs) = 
    Polynomial $ (a <> b) : (runPolynomial $ Polynomial as <> Polynomial bs)

instance Monoid a => Monoid (Polynomial a) where
  mempty = Polynomial [mempty]

{- |
The value a:p corresponds to the polynomial @a + px@, where @p@
is itself a polynomial. Multiplying two of these gives us:

@ (a + px)(b + qx) = ab + (aq + pb + pqx)x @

i.e. the discrete convolution of the two sequences.
-}
instance (Monoid a, Semiring a) => Semiring (Polynomial a) where 
  Polynomial [] >< _ = mempty
  _ >< Polynomial [] = mempty
  Polynomial (a:p) >< Polynomial (b:q) = 
    Polynomial $ (a >< b) : (runPolynomial $ (Polynomial $ fmap (a ><) q) <> (Polynomial $ fmap (>< b) p) <> (Polynomial $ zero : (runPolynomial $ Polynomial p >< Polynomial q)))
  {-# INLINE (><) #-}
 
  fromBoolean = fromBooleanDef $ Polynomial [one]

instance (Monoid a, Closed a) => Closed (Polynomial a) where 

  star (Polynomial []) = mempty
  star (Polynomial (a:p)) = 
    r where r = (Polynomial [star a]) >< (Polynomial $ one:(runPolynomial (Polynomial p >< r)))
{-
--TODO how is this related to These / Warning?.


instance (Monoid r) => Semiring (Polynomial r)
[] >< _ = []
_ >< [] = []


closure [] = one
closure (a:p) = r where r = [closure a] >< (one:(p >< r))

-}



{-
onE = Poly $ Map.singleton 1 (1::Int)
two = Poly $ Map.singleton 2 (1::Int)
three = Poly $ Map.singleton 3 (1::Int)
four = Poly $ Map.singleton 4 (1::Int)

(four <> three) >< (onE <> two <> three)
-}

-- | Univariate polynomials over an arbitrary semiring.
newtype Poly a = Poly { runPoly :: Map.Map Natural a }
  deriving (Eq, Ord, Show, Functor, Generic, GenUnchecked, GenValid, Typeable, Validity)
  deriving Num via (N (Poly a))


mono :: Natural -> a -> Poly a
mono pow coef = Poly $ Map.singleton pow coef

-- TODO props: eval zero == const coeff, eval one == sum of all coeffs
evalPoly :: (Monoid a, Semiring a) => a -> Poly a -> a
evalPoly x (Poly p) = flip Map.foldMapWithKey p $ \k a -> (foldMap' id (rep [x] k)) >< a



instance Semigroup a => Semigroup (Poly a) where
  (Poly xs) <> (Poly ys) = Poly $ Map.unionWith (<>) xs ys


instance Monoid a => Monoid (Poly a) where
  mempty = Poly $ Map.singleton 0 mempty


instance (Monoid a, Semiring a) => Semiring (Poly a) where
  Poly xs >< Poly ys = Poly $ Map.fromListWith (<>) 
     [ (k <> l, v >< u) | (k, v) <- Map.toList xs, (l, u) <- Map.toList ys ]
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ Poly (Map.singleton mempty one)

instance (Monoid a, Dioid a) => Dioid (Poly a) where
  Poly x `ord` Poly y = Map.isSubmapOfBy ord x y

-- Bivariate polynomial over an arbitrary semiring.
newtype Poly2 a = Poly2 { runPoly2 :: Map.Map (Natural, Natural) a } 
  deriving (Eq, Ord, Show, Functor, Generic, GenUnchecked, GenValid, Typeable, Validity)  
  deriving Num via (N (Poly2 a))

instance Semigroup a => Semigroup (Poly2 a) where
  (Poly2 xs) <> (Poly2 ys) = Poly2 $ Map.unionWith (<>) xs ys


instance Monoid a => Monoid (Poly2 a) where
  mempty = Poly2 $ Map.singleton (0,0) mempty

instance (Monoid a, Semiring a) => Semiring (Poly2 a) where
  Poly2 xs >< Poly2 ys = Poly2 $ Map.fromListWith (<>) 
     [ (k <> l, v >< u) | (k, v) <- Map.toList xs, (l, u) <- Map.toList ys ]
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ Poly2 (Map.singleton mempty one)



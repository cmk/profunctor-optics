{-# Language ConstrainedClassMethods #-}

module Data.Semiring.Property (
  -- * Properties of pre-semirings & semirings
    neutral_addition
  , neutral_multiplication 
  , associative_addition 
  , associative_multiplication 
  , distributive 
  , distributive_finite1 

  -- * Properties of non-unital semirings
  , nonunital

  -- * Properties of unital semirings
  , unital 
  , annihilative_multiplication 
  , distributive_finite 
  , homomorphism_boolean 

  -- * Properties of closed semirings
  , closure_pstable
  , closure_paffine 
  , closure_stable 
  , closure_affine 
  , idempotent_star

  -- * Additional optional properties
  -- ** Absorbativity
  , absorbative_addition
  , absorbative_addition'
  , absorbative_multiplication
  , absorbative_multiplication' 
  -- ** Annihilativity 
  , annihilative_addition 
  , annihilative_addition' 
  -- ** Cancellativity  
  , cancellative_addition 
  , cancellative_multiplication 
  -- ** Commutativity
  , commutative_addition 
  , commutative_multiplication
  -- ** Distributivity  
  , distributive_cross1 
  , distributive_cross 
  , codistributive
) where

import Data.List (unfoldr)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Semiring
import P
import Orphans ()

import Test.Property.Util ((<==>),(==>))
import qualified Test.Property as Prop


-- No additive or multiplicative unit.
foldPresemiring :: Semiring r => (a -> r) -> NonEmpty (NonEmpty a) -> r
foldPresemiring = foldMap1 . foldMap1'

-- No multiplicative unit.
foldNonunital :: (Monoid r, Semiring r) => (a -> r) -> [NonEmpty a] -> r
foldNonunital = foldMap . foldMap1'

-- Additive & multiplicative units.
-- Note this function will zero out if there is no multiplicative unit. 
foldUnital :: (Monoid r, Semiring r) => (a -> r) -> [[a]] -> r
foldUnital = foldMap . foldMap'


------------------------------------------------------------------------------------
-- Properties of pre-semirings & semirings

-- | \( \forall a \in R: (z + a) = a \)
--
-- A (pre-)semiring with a right-neutral additive unit must satisfy:
--
-- @
-- 'neutral_addition' 'zero' ≡ const True
-- @
-- 
-- Or, equivalently:
--
-- @
-- 'zero' '<>' r ≡ r
-- @
--
neutral_addition :: (Eq r, Semigroup r) => r -> r -> Bool
neutral_addition = Prop.neutral (<>)


-- | \( \forall a \in R: (o * a) = a \)
--
-- A (pre-)semiring with a right-neutral multiplicative unit must satisfy:
--
-- @
-- 'neutral_multiplication' 'one' ≡ const True
-- @
-- 
-- Or, equivalently:
--
-- @
-- 'one' '><' r ≡ r
-- @
--
neutral_multiplication :: (Eq r, Semiring r) => r -> r -> Bool
neutral_multiplication = Prop.neutral (><) 



-- | \( \forall a, b, c \in R: (a + b) + c = a + (b + c) \)
--
-- Addition in /R/ must be associative.
--
-- This should be verified by the underlying 'Semigroup' instance,
-- but is included here for completeness.
--
associative_addition :: (Eq r, Semigroup r) => r -> r -> r -> Bool
associative_addition = Prop.associative (<>)


-- | \( \forall a, b, c \in R: (a * b) * c = a * (b * c) \)
--
-- Multiplication in /R/ must be associative.
--
associative_multiplication :: (Eq r, Semiring r) => r -> r -> r -> Bool
associative_multiplication = Prop.associative (><)


-- | \( \forall a, b, c \in R: (a + b) * c = (a * c) + (b * c) \)
--
-- /R/ must right-distribute multiplication.
--
-- When /R/ is a functor and the semiring structure is derived from 'Alternative', 
-- this translates to: 
--
-- @
-- (a '<|>' b) '*>' c = (a '*>' c) '<|>' (b '*>' c)
-- @  
--
-- See < https://en.wikibooks.org/wiki/Haskell/Alternative_and_MonadPlus >.
--
distributive :: (Eq r, Semiring r) => r -> r -> r -> Bool
distributive = Prop.distributive (<>) (><)


-- | \( \forall M \geq 1; a_1 \dots a_M, b \in R: (\sum_{i=1}^M a_i) * b = \sum_{i=1}^M a_i * b \)
--
-- /R/ must right-distribute multiplication over finite (non-empty) sums.
--
-- This follows from 'distributive' and the universality of 'fold1'.
--
distributive_finite1 :: (Eq r, Semiring r) => NonEmpty r -> r -> Bool
distributive_finite1 as b = fold1 as >< b == foldMap1 (>< b) as


------------------------------------------------------------------------------------
-- Properties of non-unital semirings

-- | \( \forall a, b \in R: a * b = a * b + b \)
--
-- If /R/ is non-unital (i.e. one equals zero) then it will instead satisfy 
-- a right-absorbtion property. 
--
-- This follows from right-neutrality and right-distributivity.
--
-- Compare 'codistributive' and 'closure_stable'.
--
-- When /R/ is also left-distributive we get: \( \forall a, b \in R: a * b = a + a * b + b \)
--
-- See also 'Data.Warning' and < https://blogs.ncl.ac.uk/andreymokhov/united-monoids/#whatif >.
--
nonunital :: forall r. (Eq r, Monoid r, Semiring r) => r -> r -> Bool
nonunital a b = not (unital (one @r)) ==> a >< b == a >< b <> b


------------------------------------------------------------------------------------
-- Properties of unital semirings

-- | \( 1 \neq 0 \)
-- 
-- If /R/ is unital then it must have a distinguished multiplicative unit:
--
-- @
-- 'unital' one ≡ True
-- @
--
unital :: (Eq r, Monoid r, Semiring r) => r -> Bool
unital o = zero /= o


-- | \( \forall a \in R: (z * a) = u \)
--
-- A /R/ is unital then its addititive unit must be right-annihilative, i.e.:
--
-- @
-- 'annihilative_multiplcation' 'zero' ≡ const True
-- @
--
-- Or, equivalently:
--
-- @
-- 'zero' '><' r ≡ 'zero'
-- @
--
-- For 'Alternative' instances this property translates to:
--
-- @
-- 'empty' '<*>' x ≡ 'empty'
-- @
--
-- All right semirings must have a right-absorbative addititive unit.
--
annihilative_multiplication :: (Eq r, Monoid r, Semiring r) => r -> Bool
annihilative_multiplication r = Prop.annihilative (><) zero r


-- | \( \forall M \geq 0; a_1 \dots a_M, b \in R: (\sum_{i=1}^M a_i) * b = \sum_{i=1}^M a_i * b \)
--
-- /R/ must right-distribute multiplication between finite sums.
--
-- This follows from 'distributive' & 'neutral_multiplication'.
--
distributive_finite :: (Eq r, Monoid r, Semiring r) => [r] -> r -> Bool
distributive_finite as b = fold as >< b == foldMap (>< b) as


-- | 'fromBoolean' must be a semiring homomorphism into /R/.
--
homomorphism_boolean :: forall r. (Eq r, Monoid r, Semiring r) => Bool -> Bool -> Bool
homomorphism_boolean i j =
  fromBoolean True     == (one @r) &&
  fromBoolean False    == (zero @r) &&
  fromBoolean (i && j) == fi >< fj    && 
  fromBoolean (i || j) == fi <> fj 

  where fi :: r = fromBoolean i
        fj :: r = fromBoolean j


------------------------------------------------------------------------------------
-- Properties of closed semirings


-- | \( 1 + \sum_{i=1}^{P+1} a^i = 1 + \sum_{i=1}^{P} a^i \)
--
-- If /a/ is p-stable for some /p/, then we have:
--
-- @
-- 'powers' p a ≡ a '><' 'powers' p a '<>' 'one'  ≡ 'powers' p a '><' a '<>' 'one' 
-- @
--
-- If '<>' and '><' are idempotent then every element is 1-stable:
--
-- @ a '><' a '<>' a '<>' 'one' = a '<>' a '<>' 'one' = a '<>' 'one' @
--
closure_pstable :: (Eq r, Monoid r, Semiring r) => Natural -> r -> Bool
closure_pstable p a = powers p a == powers (p <> one) a

-- | \( x = a * x + b \Rightarrow x = (1 + \sum_{i=1}^{P} a^i) * b \)
--
-- If /a/ is p-stable for some /p/, then we have:
--
closure_paffine :: (Eq r, Monoid r, Semiring r) => Natural -> r -> r -> Bool
closure_paffine p a b = closure_pstable p a ==> x == a >< x <> b 
  where x = powers p a >< b


-- | \( \forall a \in R : a^* = a^* * a + 1 \)
--
-- Closure is /p/-stability for all /a/ in the limit as \( p \to \infinity \).
--
-- One way to think of this property is that all geometric series
-- "converge":
--
-- \( \forall a \in R : 1 + \sum_{i \geq 1} a^i \in R \)
--
closure_stable :: (Eq r, Monoid r, Closed r) => r -> Bool
closure_stable a = star a == star a >< a <> one

closure_stable' :: (Eq r, Monoid r, Closed r) => r -> Bool
closure_stable' a = star a == one <> a >< star a

closure_affine :: (Eq r, Monoid r, Closed r) => r -> r -> Bool
closure_affine a b = x == a >< x <> b where x = star a >< b

-- If /R/ is closed then 'star' must be idempotent:
--
-- @'star' ('star' x) == 'star' x@
--
idempotent_star :: (Eq r, Closed r) => r -> Bool
idempotent_star = Prop.idempotent star


------------------------------------------------------------------------------------
-- Additional optional properties of certain subclasses of 'Semiring'.


-- | \( \forall a, b \in R: a * b + b = b \)
--
-- Right-additive absorbativity is a generalized form of idempotency:
--
-- @
-- 'absorbative_addition' 'one' a ≡ a <> a == a
-- @
--
absorbative_addition :: (Eq r, Semiring r) => r -> r -> Bool
absorbative_addition a b = a >< b <> b == b


-- | \( \forall a, b \in R: b + b * a = b \)
--
-- Left-additive absorbativity is a generalized form of idempotency:
--
-- @
-- 'absorbative_addition' 'one' a ≡ a <> a == a
-- @
--
absorbative_addition' :: (Eq r, Semiring r) => r -> r -> Bool
absorbative_addition' a b = b <> b >< a == b



-- | \( \forall a, b \in R: (a + b) * b = b \)
--
-- Right-mulitplicative absorbativity is a generalized form of idempotency:
--
-- @
-- 'absorbative_multiplication' 'zero' a ≡ a '><' a == a
-- @
--
-- See < https://en.wikipedia.org/wiki/Absorption_law >.
--
absorbative_multiplication :: (Eq r, Semiring r) => r -> r -> Bool
absorbative_multiplication a b = (a <> b) >< b == b


-- | \( \forall a, b \in R: b * (b + a) = b \)
--
-- Left-mulitplicative absorbativity is a generalized form of idempotency:
--
-- @
-- 'absorbative_multiplication'' 'zero' a ≡ a '><' a == a
-- @
--
-- See < https://en.wikipedia.org/wiki/Absorption_law >.
--
absorbative_multiplication' :: (Eq r, Semiring r) => r -> r -> Bool
absorbative_multiplication' a b = b >< (b <> a) == b


-- | \( \forall a \in R: o + a = o \)
--
-- A unital semiring with a right-annihilative muliplicative unit must satisfy:
--
-- @
-- 'one' <> a ≡ 'one'
-- @
--
-- For a dioid this is equivalent to:
-- 
-- @
-- ('one' '<~') ≡ ('one' '==')
-- @
--
-- For 'Alternative' instances this is the left-catch law:
--
-- @
-- 'pure' a '<|>' x ≡ 'pure' a
-- @
--
annihilative_addition :: (Eq r, Monoid r, Semiring r) => r -> Bool
annihilative_addition r = Prop.annihilative (<>) one r


-- | \( \forall a \in R: a + o = o \)
--
-- A unital semiring with a left-annihilative muliplicative unit must satisfy:
--
-- @
-- a '<>' 'one' ≡ 'one'
-- @
--
-- Note that the left-annihilative property is too strong for many instances. 
-- This is because it requires that any effects that /r/ generates be undone.
--
-- See < https://winterkoninkje.dreamwidth.org/90905.html >.
--
annihilative_addition' :: (Eq r, Monoid r, Semiring r) => r -> Bool
annihilative_addition' r = Prop.annihilative' (<>) one r


-- | \( \forall a, b, c \in R: a + b = a + c \Rightarrow b = c \)
--
-- If /R/ is right-cancellative wrt addition then for all /a/
-- the section /(a <>)/ is injective.
--
cancellative_addition :: (Eq r, Semigroup r) => r -> r -> r -> Bool
cancellative_addition a = Prop.injective (a <>)


-- | \( \forall a, b, c \in R: a * b = a * c \Rightarrow b = c \)
--
-- If /R/ is right-cancellative wrt multiplication then for all /a/
-- the section /(a ><)/ is injective.
--
cancellative_multiplication :: (Eq r, Semiring r) => r -> r -> r -> Bool
cancellative_multiplication a = Prop.injective (a ><)


-- | \( \forall a, b \in R: a + b = b + a \)
--
commutative_addition :: (Eq r, Semigroup r) => r -> r -> Bool
commutative_addition = Prop.commutative (<>)


-- | \( \forall a, b \in R: a * b = b * a \)
--
commutative_multiplication :: (Eq r, Semiring r) => r -> r -> Bool
commutative_multiplication = Prop.commutative (><)


-- | \( \forall M,N \geq 1; a_1 \dots a_M, b_1 \dots b_N \in R: (\sum_{i=1}^M a_i) * (\sum_{j=1}^N b_j) = \sum_{i=1 j=1}^{i=M j=N} a_i * b_j \)
--
-- If /R/ is also left-distributive then it supports (non-empty) cross-multiplication.
--
distributive_cross1 :: (Eq r, Semiring r) => NonEmpty r -> NonEmpty r -> Bool
distributive_cross1 as bs = fold1 as >< fold1 bs == cross1 as bs


-- | \( \forall M,N \geq 0; a_1 \dots a_M, b_1 \dots b_N \in R: (\sum_{i=1}^M a_i) * (\sum_{j=1}^N b_j) = \sum_{i=1 j=1}^{i=M j=N} a_i * b_j \)
--
-- If /R/ is also left-distributive then it supports cross-multiplication.
--
distributive_cross :: (Eq r, Monoid r, Semiring r) => [r] -> [r] -> Bool
distributive_cross as bs = fold as >< fold bs == cross as bs


-- | \( \forall a, b, c \in R: c + (a * b) \equiv (c + a) * (c + b) \)
--
-- A right-codistributive semiring has a right-annihilative muliplicative unit:
--
-- @ 'codistributive' 'one' a 'zero' ≡ 'one' == 'one' '<>' a @
--
-- idempotent mulitiplication:
--
-- @ 'codistributive' 'zero' 'zero' a ≡ a == a '><' a @
--
-- and idempotent addition:
--
-- @ 'codistributive' a 'zero' a ≡ a == a '<>' a @
--
-- Furthermore if /R/ is commutative then it is a right-distributive lattice.
--
codistributive :: (Eq r, Semiring r) => r -> r -> r -> Bool
codistributive = Prop.distributive' (><) (<>)

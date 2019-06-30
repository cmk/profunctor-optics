module Data.Dioid.Property (
  -- * Properties of pre-dioids & dioids
    order 
  , order_preorder 
  , order_reflexive
  , order_transitive 

  -- * Properties of dioids
  , order_positive_addition
  , order_monotone_boolean

  -- * Properties of closed dioids
  , order_monotone_star
  , order_adjunction

  -- * Additional optional properties
  -- ** Order
  , order_total
  , order_least
  , order_annihilative
  -- ** Monotonicity
  , order_monotone_addition
  , order_monotone_multiplication
  -- ** Positivity
  , order_positive_multiplication
) where

import Data.Semiring
import Data.Semiring.Property
import Data.Dioid

import P

import Test.Property ((<==>),(==>))
import qualified Test.Property as Prop

------------------------------------------------------------------------------------
-- Properties of pre-dioids & dioids


-- | '<~' is an order relation relative to '<>'.
--
-- In other words for all /a/ we have:
--
-- @
-- (a '=~') ≡ (a '==')
-- @
--
-- A monoid with this relation is referred to as canonically-ordered.
--
order :: Dioid r => r -> r -> Bool
order a b = a =~ b <==> a == b 


-- | '<~' is a preorder relation relative to '<>'.
-- 
order_preorder :: Dioid r => r -> r -> Bool
order_preorder a b = a <~ (a <> b)


-- | \( \forall a: (a \leq a) \)
--
-- '<~' is a reflexive order relation.
--
order_reflexive :: Dioid r => r -> Bool
order_reflexive = Prop.reflexive (<~)


-- | \( \forall a, b, c: ((a \leq b) \wedge (b \leq c)) \Rightarrow (a \leq c) \)
--
-- '<~' is a transitive order relation.
--
order_transitive :: Dioid r => r -> r -> r -> Bool
order_transitive = Prop.transitive (<~)


------------------------------------------------------------------------------------
-- Properties of dioids

-- |  \( \forall a, b: a + b = 0 \Rightarrow a = 0 \wedge b = 0 \)
--
-- For a dioid this follows from 'order' and 'neutral_addition'.
--
order_positive_addition :: (Eq r, Monoid r) => r -> r -> Bool
order_positive_addition a b = a <> b == mempty ==> a == mempty && b == mempty


-- | \( \forall a, b: a \leq b \Rightarrow f a \leq f b
--
-- 'fromBoolean' is a Dioid homomorphism (i.e. a monotone semiring homomorphism)
--
order_monotone_boolean :: forall r. (Monoid r, Dioid r) => Bool -> Bool -> Bool
order_monotone_boolean = Prop.monotone_on (<~) fromBoolean


------------------------------------------------------------------------------------
-- Properties of closed dioids

-- If @r@ is a closed dioid then 'star' must be monotone:
--
-- @x '<~' y ==> 'star' x '<~' 'star' y@
--
order_monotone_star :: (Dioid r, Closed r) => r -> r -> Bool
order_monotone_star = Prop.monotone_on (<~) star


-- | \( \forall a: f a \# b \Leftrightarrow a \# g b \)
--
-- /f/ and /g/ form a Galois connection wrt the canonical preorder.
--
-- Note that this requires that /f/ and /g/ be monotone functions.
--
-- When this property holds, /f/ forms the left adjoint and /g/ the right 
-- adjoint of the connection.
--
order_adjunction :: Dioid r => (r -> r) -> (r -> r) -> r -> r -> Bool 
order_adjunction f g a b = 
  Prop.monotone_on (<~) f a b && 
  Prop.monotone_on (<~) g a b ==> Prop.adjoint_on (<~) f g a b


------------------------------------------------------------------------------------
-- Additional optional properties

-- | '<~' is a total order relation.
--
-- If this property holds then an 'Ord' instance may be defined for @r@.
--
order_total :: Dioid r => r -> r -> Bool
order_total a b = a <~? b


-- | There is a unique least element of @r@.
--
-- When this holds the least element must be 'zero'.
--
order_least :: Dioid r => r -> r -> Bool
order_least o a = o <~? a ==> o <~ a 


-- | '<~' is consistent with annihilativity.
--
-- This means that a dioid with an annihilative multiplicative unit must satisfy:
--
-- @
-- ('one' <~) ≡ ('one' ==)
-- @
--
-- Compare 'order'.
--
order_annihilative :: (Eq r, Dioid r) => r -> r -> Bool
order_annihilative a b = a <~ b <==> a == b 


-- | \( \forall a, b, c: b \leq c \Rightarrow a+b \leq a+c
--
-- Compare 'cancellative_addition'.
--
order_monotone_addition :: Dioid r => r -> r -> r -> Bool
order_monotone_addition a = Prop.monotone_on (<~) (a <>)


-- | \( \forall a, b, c: b \leq c \Rightarrow a*b \leq a*c
--
-- Compare 'cancellative_multiplication'.
--
order_monotone_multiplication :: Dioid r => r -> r -> r -> Bool
order_monotone_multiplication a = Prop.monotone_on (<~) (a ><)


-- |  \( \forall a, b: a * b = 0 \Rightarrow a = 0 \vee b = 0 \)
--
order_positive_multiplication :: (Dioid r, Monoid r, Semiring r) => r -> r -> Bool
order_positive_multiplication a b = a >< b == zero ==> a == zero || b == zero

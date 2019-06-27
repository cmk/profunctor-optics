module Data.Tropical where

import Data.Semiring
import Data.Dioid
import Data.Typeable (Typeable)
import Data.Validity
import Data.GenValidity

import GHC.Generics                (Generic, Generic1)
import Foreign.Storable            (Storable)

import P hiding (Min(..),Max(..))
import Orphans ()

{-
Definition 6.7.1. We call idempotent-invertible dioid a dioid (E, ⊕, ⊗) which has a
commutative idempotent monoid structure for ⊕ and a group structure for ⊗ (every
element of E\{ε} having an inverse for ⊗).

Definition 6.7.2. We call selective-invertible-dioid a dioid (E, ⊕, ⊗) which has a
selective monoid structure for ⊕ and a group structure for ⊗ (every element of E\{ε}
having an inverse for ⊗).

Example 6.6.4. Let us take for E the set of nonnegative reals R+ ∪ {+∞} and let us
define the operations ⊕ and ⊗ as:
∀a, b ∈ E: a ⊕ b = Min{a, b}
∀a, b ∈ E: a ⊗ b = a + b (addition of reals)
(E, ⊕) is a selective monoid with neutral element ε = +∞, and (E, ⊗) is a
cancellative monoid with neutral element e = 0.
The structure (E, ⊕, ⊗) above is therefore a selective-cancellative dioid. ||

Note that, in the terminology of the theory of languages and automata, selectiveinvertible dioids such as Min-Plus or Max-Plus dioids are sometimes referred to as
Tropical semirings 

We call selective-invertible-dioid a dioid (E, ⊕, ⊗) which has a
selective monoid structure for ⊕ and a group structure for ⊗ (every element of E\{ε}
having an inverse for ⊗).

-}

-- | 
--   @'Min' a@ is equivalent to the semiring
--   \( (a \cup \{+\infty\}, \oplus, \otimes) \), where \( x \oplus y = min\{x,y\}\) and \(x \otimes y = x <> y\).
--
-- Note that the underlying monoid instance must be right-distributive
-- wrt 'min':
-- @
-- ('min' b c) <> a == 'min' (b '<>' a) (c '<>' a)
-- @
-- 
data Min a = Min !a | PInf
  deriving (Eq, Show, Functor, Generic, Typeable)
  deriving Num via (N (Min a))

instance GenUnchecked a => GenUnchecked (Min a)
instance GenValid a => GenValid (Min a)
instance Validity a => Validity (Min a)

type MinFirst a = Min (First a)
type MinLast a = Min (Last a)


instance Ord a => Ord (Min a) where
  Min a <= Min b = a <= b
  a <= PInf = True
  PInf <= a = False
  
instance Ord a => Semigroup (Min a) where
  Min a <> Min b = Min $ min a b
  a <> PInf = a
  PInf <> a = a

instance Ord a => Monoid (Min a) where
  mempty = PInf

instance (Monoid a, Ord a) => Semiring (Min a) where
  Min a >< Min b = Min $ a <> b
  _ >< PInf = PInf
  PInf >< _ = PInf
  fromBoolean = fromBooleanDef $ Min mempty

instance (Monoid a, Ord a) => Dioid (Min a) where
  ord = (>=)

instance Closed (Min Natural) where
  star PInf = one
  star _    = PInf
  



-- | 
--
--   @'Max' a@ is equivalent to the semiring
--   \( (a \cup \{-\infty\}, \oplus, \otimes) \), where \( x \oplus y = max\{x,y\}\) and \(x \otimes y = x + y\).

-- Note that the underlying monoid instance must be right-distributive
-- wrt 'max':
-- @
-- ('max' b c) <> a == 'max' (b '<>' a) (c '<>' a)
-- @
-- 
data Max a = NInf | Max !a
  deriving (Eq, Show, Functor, Generic, Typeable)
  deriving Num via (N (Max a))

instance GenUnchecked a => GenUnchecked (Max a)
instance GenValid a => GenValid (Max a)
instance Validity a => Validity (Max a)

type MaxFirst a = Max (First a)
type MaxLast a = Max (Last a)

instance Ord a => Ord (Max a) where
  Max a <= Max b = a <= b
  NInf <= a = True
  a <= NInf = False
  
instance Ord a => Semigroup (Max a) where
  Max a <> Max b = Max $ max a b
  a <> NInf = a
  NInf <> a = a

instance Ord a => Monoid (Max a) where
  mempty = NInf

instance (Monoid a, Ord a) => Semiring (Max a) where
  Max a >< Max b = Max $ a <> b
  _ >< NInf = NInf
  NInf >< _ = NInf


  fromBoolean = fromBooleanDef $ Max mempty

instance (Monoid a, Ord a) => Dioid (Max a) where
  ord = (<=)



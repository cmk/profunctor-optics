{-# Language ConstrainedClassMethods #-}

module Data.Semiring.Property where

import Data.List.NonEmpty (NonEmpty(..))
import Data.Semiring
import P
import Orphans ()

iff = xnor

------------------------------------------------------------------------------------
-- | Properties of pre-semirings & semirings.

-- | The map @('><' c)@ preserves '<>'. See Fong and Spivak (Definition 1.92.)
--
-- When @r@ is a functor and the semiring structure is derived from 'Alternative', 
-- this translates to: @(f <|> g) <*> a = (f <*> a) <|> (g <*> a)@  
-- See https://en.wikibooks.org/wiki/Haskell/Alternative_and_MonadPlus#Other_suggested_laws
--
-- When @r@ is a functor and the semiring structure is derived from 'Selective'

-- | Multiplication should right-distribute across addition.
prop_distributive :: (Eq r, Semiring r) => r -> r -> r -> Bool
prop_distributive a b c = (a <> b) >< c == (a >< c) <> (b >< c)

-- | Multiplication should right-distribute across finite non-empty sums.
prop_distributive_finite1 :: (Eq r, Semiring r) => r -> NonEmpty r -> Bool
prop_distributive_finite1 a bs = fold1 bs >< a == foldMap1 (>< a) bs

prop_associative_addition :: (Eq r, Monoid r) => r -> r -> r -> Bool
prop_associative_addition a b c = (a <> b) <> c == a <> (b <> c)

prop_associative_multiplication :: (Eq r, Semiring r) => r -> r -> r -> Bool
prop_associative_multiplication a b c = (a >< b) >< c == a >< (b >< c)

--prop_universal_addition / foldSemiring1

--prop_universal_multiplication

---- Neutrality.

-- | A pre-semiring with a (right) neutral additive unit must satisfy:
--
-- @
-- 'prop_neutral_addition' 'zero' ≡ const True
-- @
-- 
-- Or, equivalently:
--
-- @
-- 'zero' <> r ≡ r
-- @
--
-- All (right) semirings must have a (right) neutral multiplicative unit.
-- 
prop_neutral_addition :: (Eq r, Semiring r) => r -> r -> Bool
prop_neutral_addition o r = o <> r == r


-- | A pre-semiring with a (right) neutral multiplicative unit must satisfy:
--
-- @
-- 'prop_neutral_multiplication' 'one' ≡ const True
-- @
-- 
-- Or, equivalently:
--
-- @
-- 'one' >< r ≡ r
-- @
--
-- All (right) semirings must have a (right) neutral multiplicative unit.
-- 
prop_neutral_multiplication :: (Eq r, Semiring r) => r -> r -> Bool
prop_neutral_multiplication o r = o >< r == r


-- | A pre-semiring with a (right) annihilative addititive unit must satisfy:
--
-- @
-- 'prop_annihilative_multiplcation' 'zero' ≡ const True
-- @
--
-- Or, equivalently:
--
-- @
-- 'zero' >< r ≡ 'zero'
-- @
--
-- For 'Alternative' instances this property translates to:
--
-- @
-- 'empty' <*> x ≡ 'empty'
-- @
--
-- All (right) semirings must have a (right) absorbative addititive unit.
--
prop_annihilative_multiplication :: (Eq r, Semiring r) => r -> r -> Bool
prop_annihilative_multiplication z r = z >< r == z


------------------------------------------------------------------------------------
-- | Properties of semirings

-- See Gondran and Minoux p. 31
-- | Multiplication should right-distribute across finite sums.
prop_distributive_finite :: (Eq r, Monoid r, Semiring r) => r -> [r] -> Bool
prop_distributive_finite a bs = fold bs >< a == foldMap (>< a) bs


-- | 'fromBoolean' is a semiring homomorphism.
prop_homomorphism_boolean :: forall r. (Eq r, Monoid r, Semiring r) => Bool -> Bool -> Bool 
prop_homomorphism_boolean i j = fromBoolean (i && j) == fi >< fj && fromBoolean (i || j) == fi <> fj 
  where fi :: r = fromBoolean i
        fj :: r = fromBoolean j

{-
-- | 'fromNatural' is a semiring homomorphism.
prop_homomorphism_natural :: forall r. (Eq r, Monoid r, Semiring r) => Natural -> Natural -> Bool 
prop_homomorphism_natural i j = fromNatural (i * j) == fi >< fj && fromNatural (i + j) == fi <> fj 
  where fi :: r = fromNatural i
        fj :: r = fromNatural j
-}


------------------------------------------------------------------------------------
-- | Additional (optional) properties of certain subclasses of 'Semiring'.

-- | The existence of distinguished additive and multiplicative units distinguishes 
-- a semiring (resp. dioid) from a pre-semiring (pre-dioid).
prop_unital :: (Eq r, Monoid r, Semiring r) => r -> Bool
prop_unital o = zero /= o


---- Annihilativity

-- A semiring with a (right) annihilative muliplicative unit must satisfy:
--
-- @
-- 'one' <> r ≡ 'one'
-- @
--
-- For a dioid this is equivalent to:
-- 
-- @
-- ('one' <~) ≡ ('one' ==)
-- @
--
-- For 'Alternative' instances this is the so-called 'left catch' law:
--
-- @
-- 'pure' a <|> x ≡ 'pure' a
-- @
--
prop_annihilative_addition :: (Eq r, Semiring r) => r -> r -> Bool
prop_annihilative_addition o r = o <> r == o



-- A semiring with a (left) annihilative muliplicative unit must satisfy:
--
-- @
-- r <> 'one' ≡ 'one'
-- @
--
-- Note that the left absorbtion property is too strong for many instances. 
-- This is because it requires that any effects that @r@ has can be undone.
-- See https://winterkoninkje.dreamwidth.org/90905.html
--
prop_annihilative_addition' :: (Eq r, Semiring r) => r -> r -> Bool
prop_annihilative_addition' = flip prop_annihilative_addition




---- Commutativity

prop_commutative_addition :: (Eq r, Semigroup r) => r -> r -> Bool
prop_commutative_addition a b = a <> b == b <> a

prop_commutative_multiplication :: (Eq r, Semiring r) => r -> r -> Bool
prop_commutative_multiplication a b = a >< b == b >< a

---- Left-sided versions of the common properties.

-- | Left multiplicative distributivity. 
prop_distributive' :: (Eq r, Semiring r) => r -> r -> r -> Bool
prop_distributive' a b c = a >< (b <> c) == (a >< b) <> (a >< c)

-- | Left additive neutrality (typically of 'zero').
prop_neutral_addition' :: (Eq r, Semiring r) => r -> r -> Bool
prop_neutral_addition' = flip prop_neutral_addition

-- | Left multiplicative neutrality (typically of 'one').
prop_neutral_multiplication' :: (Eq r, Semiring r) => r -> r -> Bool
prop_neutral_multiplication' = flip prop_neutral_multiplication

-- | Left multiplicative absorbtion (typically of 'zero').
prop_annihilative_multiplication' :: (Eq r, Semiring r) => r -> r -> Bool
prop_annihilative_multiplication' = flip prop_annihilative_multiplication


-- | Multiplication should left-distribute across finite sums.
prop_distributive_finite1' :: (Eq r, Semiring r) => r -> NonEmpty r -> Bool
prop_distributive_finite1' a bs = a >< fold1 bs == foldMap1 (a ><) bs

-- | Multiplication should left-distribute across finite sums.
prop_distributive_finite' :: (Eq r, Monoid r, Semiring r) => r -> [r] -> Bool
prop_distributive_finite' a bs = a >< fold bs == foldMap (a ><) bs


-- | Multiplication should bi-directionally distribute across finite sums.
-- 
prop_distributive_cross1 :: (Eq r, Semiring r) => NonEmpty r -> NonEmpty r -> Bool
prop_distributive_cross1 as bs = fold1 as >< fold1 bs == cross1 as bs

-- | Multiplication should bi-directionally distribute across finite sums.
prop_distributive_cross :: (Eq r, Monoid r, Semiring r) => [r] -> [r] -> Bool
prop_distributive_cross as bs = fold as >< fold bs == cross as bs


---- Idempotency

-- G & M p. 15, Proposition 3.4.5 .
prop_idempotent_addition :: (Eq r, Semigroup r) => Natural -> r -> Bool
prop_idempotent_addition n r = n >= 1 ==> r == foldMap1 id (r :| rep [r] (n-1))


---- Absorbativity & Idempotency 
-- (See https://en.wikipedia.org/wiki/Absorption_law)
-- https://en.wikipedia.org/wiki/Lattice_(order)#Lattices_as_algebraic_structures

-- Given 'prop_absorbative_multiplication', 'prop_distributive' & 'prop_neutral_mulitplication'
-- we can derive the following weak absorbtion property: @a == a <> b >< a@.
prop_absorbative_weak :: (Eq r, Monoid r, Semiring r) => r -> r -> Bool
prop_absorbative_weak a b =
  prop_distributive one a b &&
  prop_neutral_multiplication one b &&
  prop_annihilative_multiplication zero a ==> a == a <> b >< a

-- See Gondran and Minoux p. 44 (Exercise 4)


-- | @(a >< b) <> c ≡ a >< (b <> c)@
-- When @r@ is a functor and the semiring structure is derived from 'Selective', 
-- this translates to: @(x *> y) <*? z ≡ x *> (y <*? z)@
prop_idempotent :: (Eq r, Semiring r) => r -> r -> r -> Bool
prop_idempotent a b c = a >< b <> c == a >< (b <> c)

-- | A generalized form of multiplicative idempotency.
--
-- @
-- 'prop_absorbative_multiplication' 'zero' a = a >< a == a
-- @
--
prop_absorbative_multiplication :: (Eq r, Semiring r) => r -> r -> Bool
prop_absorbative_multiplication z a = (z <> a) >< a == a

prop_absorbative_multiplication' :: (Eq r, Semiring r) => r -> r -> Bool
prop_absorbative_multiplication' z a = a >< (a <> z) == a

-- | A generalized form of additive idempotency.
--
-- @
-- 'prop_absorbative_addition' 'one' a = a <> a == a
-- @
--
prop_absorbative_addition :: (Eq r, Semiring r) => r -> r -> Bool
prop_absorbative_addition o a = o >< a <> a == a

prop_absorbative_addition' :: (Eq r, Semiring r) => r -> r -> Bool
prop_absorbative_addition' o a = a <> a >< o == a


---- Cancellativity

-- | Right cancellativity:
--
-- @m >< m' == m >< m''@ implies @m' == m''@
--
prop_cancellative :: (Eq r, Semiring r) => r -> r -> r -> Bool
prop_cancellative a b c = a >< b == a >< c ==> b == c

-- | Left cancellativity:
--
-- @m' >< m == m'' >< m@ implies @m' == m''@
--
prop_cancellative' :: (Eq r, Semiring r) => r -> r -> r -> Bool
prop_cancellative' a b c = a >< c == b >< c ==> a == c

---- Selectivity

prop_selective_addition :: (Eq r, Semigroup r) => r -> r -> Bool
prop_selective_addition a b = ab == a || ab == b where ab = a <> b

-- A semiring is said to be doubly selective if both operations are selective
prop_selective_multiplication :: (Eq r, Semiring r) => r -> r -> Bool
prop_selective_multiplication a b = ab == a || ab == b where ab = a >< b



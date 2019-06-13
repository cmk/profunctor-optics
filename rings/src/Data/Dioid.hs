{-# Language ScopedTypeVariables #-}

module Data.Dioid where

import Data.Bool
import Data.Semigroup
import Data.Semiring
import Data.Monoid hiding (First, Last)
import Numeric.Natural (Natural)

import Data.Functor.Contravariant
import Data.List (stripPrefix)
import Data.Maybe (isJust)

import Orphans ()

import qualified Control.Exception as Ex
import qualified Data.Set as Set

{-
import Control.Monad.Catch (MonadThrow(..))
import Control.Monad.Catch.Pure
import Control.Monad.Fail
-}

{-
An idempotent dioid is a dioid in which the addition ⊕ is idempotent.


Idempotent dioids form a particularly rich class of dioids which contains many
sub-classes, in particular:
– Doubly-idempotent dioids and distributive lattices (see Sect. 6.5);
– Doubly selective dioids (see Sect. 6.5);
– Idempotent-cancellative dioids and selective-cancellative dioids (see Sect. 6.6);
– Idempotent-invertible dioids and selective-invertible dioids (see Sect. 6.7).

A frequently encountered special case is one where addition ⊕ is not only
idempotent but also selective. A selective dioid is a dioid in which the addition ⊕ is selective (i.e.: ∀a, b ∈ E: a ⊕ b = a or b).

TODO- integrate selective applicative
-}

-- | Pre-dioids and dioids.
class Semiring r => Dioid r where 
  
  -- The (right) canonical preorder relation relative to '<>':
  -- 'ord a b' iff 'b == a <> c' for some c.
  ord :: r -> r -> Bool
  --   ord :: Equivalence r


-- | Monotone pullback to naturals.
ord' :: forall r. (Monoid r, Dioid r) => Equivalence Natural
ord' = contramap fromNatural (Equivalence ord :: Equivalence r)

implies :: Bool -> Bool -> Bool
implies a b = not a || b

--instance (Presemiring (f a), Monoid a, Applicative f) => Dioid (f a) where one = pure mempty



--prop_idempotent_zero :: Bool
--prop_idempotent_zero  

-- a ≤ b => forall x. a ⊗ x ≤ b ⊗ x 
--prop_order_compatible :: (Eq r, Dioid r) => r -> r -> Bool

------------------------------------------------------------------------------------
-- Properties of pre-dioids

-- | 'ord' is a preorder relation relative to '<>'
prop_order_preorder :: (Eq r, Dioid r) => r -> r -> r -> Bool
prop_order_preorder a b c = bool True (a <> c == b) $ ord a b

-- | 'ord' is a total order relation
prop_order_total :: (Eq r, Dioid r) => r -> r -> Bool
prop_order_total a b = bool True (a == b) $ ord a b && ord b a 

-- | If 'zero' is non-absorbing then the pre-dioid '(zero ><)' is an idempotent pre-dioid.
--prop_zero_nonabsorb_right :: (Eq r, Monoid r, Dioid r) => r -> Bool
--prop_zero_nonabsorb_right r = 

------------------------------------------------------------------------------------
-- Properties of dioids

-- | 'fromNatural' is a Dioid homomorphism (i.e. a monotone or order-preserving function)
prop_monotone :: forall r. (Monoid r, Dioid r) => Natural -> Natural -> Bool
prop_monotone a b = bool (a <= b) True $ fromNatural a `ord` (fromNatural b :: r)


-- | aka 'left catch' law for idempotent dioids
prop_one_absorb_right :: (Eq r, Monoid r, Dioid r) => r -> Bool
prop_one_absorb_right r = one <> r == one


-- See Gondran and Minoux p. 44 (Exercise 5)
prop_order_zero :: (Eq r, Monoid r, Dioid r) => r -> r -> Bool
prop_order_zero a b = bool True (a == zero && b == zero) $ a <> b /= zero

------------------------------------------------------------------------------------
-- Additional (optional) properties of certain subclasses of dioids.

{-

Note that left absorbtion (i.e. r <> one == one) is too strong for many instances:

The reason it fails is that we are essentially assuming that any "effects" that x has can be undone once we realize the whole computation is supposed to "fail". Indeed this rule is too strong to make sense for our general notion that MonadPlus provides a notion of choice or addition

https://winterkoninkje.dreamwidth.org/90905.html
-}

prop_one_absorb_left :: (Eq r, Monoid r, Dioid r) => r -> Bool
prop_one_absorb_left r = r <> one == one

-- See Gondran and Minoux p. 44 (Exercise 5)
prop_positive :: (Eq r, Monoid r, Dioid r) => r -> r -> r -> Bool
prop_positive a b c = if a <> b /= zero then True else a == zero || b == zero

-- See Gondran and Minoux p. 44 (Exercise 4)
prop_idempotent :: (Eq r, Dioid r) => r -> r -> r -> Bool
prop_idempotent a b c = (a >< b) <> c == (a <> c) >< (a <> b)

prop_selective_additive :: (Eq r, Dioid r) => r -> r -> Bool
prop_selective_additive a b = ab == a || ab == b where ab = a <> b

prop_selective_multiplicative :: (Eq r, Dioid r) => r -> r -> Bool
prop_selective_multiplicative a b = ab == a || ab == b where ab = a >< b

{-
-- | aka 'left catch' law for idempotent dioids
prop_right_absorb :: (Eq r, Dioid r) => r -> Bool
prop_right_absorb r = dempty <> r == dempty

prop_right_absorb :: (Eq r, Dioid r) => r -> Bool
prop_right_absorb r = one <> r == one


fromBoolean :: Dioid r => Bool -> r
fromBoolean False = mempty
fromBoolean True = dempty

fromNatural :: Dioid r => Natural -> r
fromNatural 0 = mempty
fromNatural _ = dempty
-}


-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------


instance Dioid Natural where

  ord = (<=)


instance Dioid () where

  ord _ _ = True


instance Dioid Bool where

  ord = implies


instance (Bounded a, Ord a) => Dioid (Max a) where

  ord = (<=)


instance (Bounded a, Ord a) => Dioid (Min a) where

  ord = (>=)


instance (Eq a, Monoid a) => Dioid [a] where

  ord a b = isJust $ stripPrefix a b


instance (Semigroup a, Eq e, Eq a) => Dioid (Either e a) where

  Right a `ord` Right b  = a == b
  Right _ `ord` _        = False
  
  Left e  `ord` Left f   = e == f
  Left _  `ord` _        = True

{-
instance Semigroup (Either a b) where
    Left _ <> b = b
    a      <> _ = a
-}

-- natural model for shortest path problems
newtype Path a = Path { runPath :: a } deriving (Eq, Show, Ord, Functor)

-- natural model for maximum capacity path & maximum weight spanning tree problems
newtype Capacity a = Capacity { runCapacity :: a }

{-
instance (Bounded a, Ord a) => Dioid (Path a) where

instance (Ord a, Bounded a, Semigroup a) => Semigroup (Path a) where (<>) = liftA2 (<>)

instance (Ord a, Bounded a, Monoid a) => Dioid (Path a) where
-}

{-
The dioid P(A∗) is the set of all languages on the alphabet
A, endowed with the operations of union ∪ and concatenation o, which is at the
basis of the theory of languages and automata.
-}

-- instance Dioid (ZipList a) where
--  ord x y = ---- analagous to 'isPrefixOf'


--instance (Monoid a, Dioid a) => Dioid (End a) where ord (End f) (End g) = 

-- Dioid instances for (R, Min, +) and (N, +, ×)

-- This is a very important class of dioids underlying a wide variety of problems, in particular many non classical path-finding problems in graphs
--instance Dioid End where



--instance Dioid Any where dempty = Any True

-- Note that this instance uses 'False' as its multiplicative unit. 
--instance Dioid All where dempty = All False

--instance Dioid a => Dioid (Maybe a) where  dempty = Just dempty -- relies on a's dempty to satisfy the right absorbtion law

--instance Monoid a => Dioid (Either e a) where dempty = pure mempty



{-

instance Semiring a => Dioid (IO a) where

  dempty = Ex.throwIO Ex.SomeException

instance (e ~ Ex.SomeException, Semiring a)  => Dioid (Either e) where

  dempty = Left $ Ex.toException Ex.

-}

--instance Monad m => Monoid (Kleisli m a)
--instance Monad m => Semigroup (Signed (Kleisli m a) ...

--instance MonadThrow m => Dioid (CatchT m a) where dempty = 


---------------------------------------------------------------------
--  Instances (contravariant)
---------------------------------------------------------------------

--deriving instance Semiring (Predicate a)

{-
Let E be a set and R (E) the set of binary relations on E. 
One verifies that R (E), endowed with the two following laws:

R ⊕ R' :  x (R ⊕ R') y iff x R y or xR'y,
R ⊗ R' : x (R ⊗ R') y iff ∃ z ∈ E with x R z and z R' y
is an idempotent dioid.

The canonical order relation corresponds to: R ≤ R' if and only if x Ry implies
x R' y, i.e. iff R is finer than R'
.
-}

-- | Binary Relations. This would be bicontravariant
newtype Relation a b = Relation { runRelation :: a -> b -> Bool }

instance Semigroup (Relation a a) where
  Relation p <> Relation q = Relation $ \a b -> p a b || q a b

instance Monoid (Relation a a) where
  mempty = Relation (\_ _ -> False)


--deriving instance Semiring a => Semiring (Op a b)



---------------------------------------------------------------------
--  Instances (containers)
---------------------------------------------------------------------

instance (Ord a, Monoid a) => Dioid (Set.Set a) where

  ord = Set.isSubsetOf

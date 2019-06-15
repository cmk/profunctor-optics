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
import Control.Selective (Under(..), Over(..), ifS)

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


dplus :: Dioid r => r -> r -> r
dplus f g = bool f g $ ord f g

dzero :: (Monoid r, Dioid r) => r
dzero = zero

-- | Monotone pullback to naturals.
ord' :: forall r. (Monoid r, Dioid r) => Equivalence Natural
ord' = contramap fromNatural (Equivalence ord :: Equivalence r)



--instance (Semiring (f a), Monoid a, Applicative f) => Dioid (f a) where one = pure mempty

implies :: Bool -> Bool -> Bool
implies a b = not a || b
{-# INLINEABLE implies #-}

infixr 0 ==>

(==>) :: Bool -> Bool -> Bool
(==>) = implies

--prop_idempotent_zero :: Bool
--prop_idempotent_zero  

-- a ≤ b => forall x. a ⊗ x ≤ b ⊗ x 
--prop_order_compatible :: (Eq r, Dioid r) => r -> r -> Bool

------------------------------------------------------------------------------------
-- | Properties of pre-dioids & dioids

-- | 'ord' is a preorder relation relative to '<>'
prop_order_preorder :: (Eq r, Dioid r) => r -> r -> r -> Bool
prop_order_preorder a b c = ord a b ==> a <> c == b

-- | 'ord' is a total order relation 
prop_order_total :: (Eq r, Dioid r) => r -> r -> Bool
prop_order_total a b = ord a b && ord b a ==> a == b

-- If 'zero' is non-absorbing then the pre-dioid '(zero ><)' is an idempotent pre-dioid.
--prop_zero_nonabsorb_right :: (Eq r, Monoid r, Dioid r) => r -> Bool
--prop_zero_nonabsorb_right r = 

------------------------------------------------------------------------------------
-- | Properties of dioids

-- | 'fromNatural' is a Dioid homomorphism (i.e. a monotone or order-preserving function)
prop_monotone :: forall r. (Monoid r, Dioid r) => Natural -> Natural -> Bool
prop_monotone a b = a <= b ==> fromNatural a `ord` (fromNatural b :: r)


-- | This is the 'left catch' law for idempotent dioids, e.g:
-- @'pure' a <|> x ≡ 'pure' a@
-- which is equivalent to 
-- @'ord' 'one' ≡ (one ==)
prop_one_absorb_right :: (Eq r, Monoid r, Dioid r) => r -> Bool
prop_one_absorb_right r = one <> r == one


prop_positive_additive :: (Eq r, Monoid r, Dioid r) => r -> r -> Bool
prop_positive_additive a b = a <> b == zero ==> a == zero && b == zero

------------------------------------------------------------------------------------
-- | Additional properties of certain subclasses of dioid.

{-

Note that left absorbtion (i.e. r <> one == one) is too strong for many instances:

The reason it fails is that we are essentially assuming that any "effects" that x has can be undone once we realize the whole computation is supposed to "fail". Indeed this rule is too strong to make sense for our general notion that MonadPlus provides a notion of choice or addition

https://winterkoninkje.dreamwidth.org/90905.html
-}

prop_one_absorb_left :: (Eq r, Monoid r, Dioid r) => r -> Bool
prop_one_absorb_left r = r <> one == one

---- Positivity

-- See Gondran and Minoux p. 44 (Exercise 5)
prop_positive_multiplicative :: (Eq r, Monoid r, Dioid r) => r -> r -> Bool
prop_positive_multiplicative a b = a >< b == zero ==> a == zero || b == zero

---- Idempotency
-- See Gondran and Minoux p. 44 (Exercise 4)

-- | @(a >< b) <> c ≡ a >< (b <> c)@
-- When @r@ is a functor and the semiring structure is derived from 'Selective', 
-- this translates to: @(x *> y) <*? z ≡ x *> (y <*? z)@
prop_idempotent :: (Eq r, Dioid r) => r -> r -> r -> Bool
prop_idempotent a b c = (a >< b) <> c == a >< (b <> c)


---- Selectivity
prop_selective_additive :: (Eq r, Dioid r) => r -> r -> Bool
prop_selective_additive a b = ab == a || ab == b where ab = a <> b

prop_selective_multiplicative :: (Eq r, Dioid r) => r -> r -> Bool
prop_selective_multiplicative a b = ab == a || ab == b where ab = a >< b

{-

fromBoolean :: Dioid r => Bool -> r
fromBoolean False = mempty
fromBoolean True = dempty

fromNatural :: Dioid r => Natural -> r
fromNatural 0 = mempty
fromNatural _ = dempty
-}

-------------------------------------------------------------------------------
-- Pre-dioids
-------------------------------------------------------------------------------

-- | 'First a' forms a pre-dioid.
instance (Eq a, Semigroup a) => Dioid (First a) where

  ord = (==)


-------------------------------------------------------------------------------
-- Dioids
-------------------------------------------------------------------------------



-- | Only the trivial dioid can have a total order relation that is constantly true.
instance Dioid () where

  ord _ _ = True


instance Dioid Bool where

  ord = implies -- not a || b -- true iff a implies b


instance Dioid Natural where

  ord = (<=)


instance (Eq r, Monoid r, Semiring r) => Dioid (Under r a) where

  ord = (==)


instance (Bounded a, Ord a) => Dioid (Max a) where

  ord = (<=)


instance (Bounded a, Ord a) => Dioid (Min a) where

  ord = (>=)


instance (Eq a, Monoid a) => Dioid [a] where

  ord a b = isJust $ stripPrefix a b


instance (Eq e, Eq a, Semigroup a) => Dioid (Either e a) where

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

{-
concat :: NonEmpty (NonEmpty a) -> NonEmpty a
concat m = m >>= id

class Semigroup m => Partitionable m where
  -- | partitionWith f c returns a list containing f a b for each a b such that a <> b = c, 
  partitionWith :: (m -> m -> r) -> m -> NonEmpty r

instance Partitionable Bool where
  partitionWith f False = f False False :| []
  partitionWith f True  = f False True :| [f True False, f True True]

instance Partitionable Natural where
  partitionWith f n = fromList [ f k (n - k) | k <- [0..n] ]

instance Partitionable () where
  partitionWith f () = f () () :| []

instance (Partitionable a, Partitionable b) => Partitionable (a,b) where
  partitionWith f (a,b) = concat $ partitionWith (\ax ay -> 
                                   partitionWith (\bx by -> f (ax,bx) (ay,by)) b) a

instance (Partitionable a, Partitionable b, Partitionable c) => Partitionable (a,b,c) where
  partitionWith f (a,b,c) = concat $ partitionWith (\ax ay -> 
                            concat $ partitionWith (\bx by -> 
                                     partitionWith (\cx cy -> f (ax,bx,cx) (ay,by,cy)) c) b) a
-}


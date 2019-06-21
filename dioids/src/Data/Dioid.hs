{-# Language ScopedTypeVariables #-}

module Data.Dioid where

import Data.Bool
import Data.Semigroup
import Data.Semiring
import Data.Monoid hiding (First, Last)
import Data.Functor.Contravariant
import Data.List (stripPrefix)
import Data.Maybe (isJust)
import Numeric.Natural (Natural)
import Data.Foldable
import Data.List.NonEmpty (NonEmpty(..))
import Orphans ()
import Control.Selective -- (Under(..), Over(..), ifS)

import qualified Control.Exception as Ex
import qualified Data.Set as Set

import P (implies, (==>))

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
--
-- A pre-dioid is a pre-semiring with a (right) canonical preorder relation relative to '<>':
-- @'ord' a b@ iff @b ≡ a <> c@ for some @c@.
--
-- A dioid is a semiring with the same property.
class Semiring r => Dioid r where 
  
  ord :: r -> r -> Bool
  --   ord :: Equivalence r

  -- left catch operator?
  --(<<) :: r -> r -> r

dplus :: Dioid r => r -> r -> r
dplus f g = bool f g $ ord f g

-- | Monotone pullback to booleans.
ord' :: forall r. (Monoid r, Dioid r) => Equivalence Bool
ord' = contramap fromBoolean (Equivalence ord :: Equivalence r)

{-

-- Selective higher-order dioids
--(>|<) :: (Selective f, forall a. Dioid (f a)) => f a -> f a -> f a



-- | Branch on a Boolean value, skipping unnecessary effects.
ifS :: Selective f => f Bool -> f a -> f a -> f a
ifS x t e = branch (bool (Right ()) (Left ()) <$> x) (const <$> t) (const <$> e)

instance (Dioid a, Selective f, Semiring f) => Dioid (f a) where 
-}


--prop_idempotent_zero :: Bool
--prop_idempotent_zero  


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

-- | 'fromBoolean' is a Dioid homomorphism (i.e. a monotone or order-preserving function)
prop_monotone_boolean :: forall r. (Monoid r, Dioid r) => Bool -> Bool -> Bool
prop_monotone_boolean a b = a <= b ==> fromBoolean a `ord` (fromBoolean b :: r)

prop_positive_additive :: (Eq r, Monoid r, Dioid r) => r -> r -> Bool
prop_positive_additive a b = a <> b == zero ==> a == zero && b == zero

-- a ≤ b => forall x. x ⊗ a ≤ x ⊗ b 
prop_left_order_multiplicative :: (Eq r, Dioid r) => r -> r -> r -> Bool
prop_left_order_multiplicative a b c = a `ord` b ==> c >< a `ord` (c >< b)

-- a ≤ b => forall x. a ⊗ x ≤ b ⊗ x 
prop_right_order_multiplicative :: (Eq r, Dioid r) => r -> r -> r -> Bool
prop_right_order_multiplicative a b c = a `ord` b ==> a >< c `ord` (b >< c)

------------------------------------------------------------------------------------
-- | Additional properties of certain subclasses of dioid.

{-

Note that left absorbtion (i.e. r <> one == one) is too strong for many instances:

The reason it fails is that we are essentially assuming that any "effects" that x has can be undone once we realize the whole computation is supposed to "fail". Indeed this rule is too strong to make sense for our general notion that MonadPlus provides a notion of choice or addition

https://winterkoninkje.dreamwidth.org/90905.html
-}

prop_left_absorbative_one  :: (Eq r, Monoid r, Semiring r) => r -> Bool
prop_left_absorbative_one r = r <> one == one

---- Positivity

-- See Gondran and Minoux p. 44 (Exercise 5)
prop_positive_multiplicative :: (Eq r, Monoid r, Semiring r) => r -> r -> Bool
prop_positive_multiplicative a b = a >< b == zero ==> a == zero || b == zero

---- Idempotency
-- See Gondran and Minoux p. 44 (Exercise 4)

-- | @(a >< b) <> c ≡ a >< (b <> c)@
-- When @r@ is a functor and the semiring structure is derived from 'Selective', 
-- this translates to: @(x *> y) <*? z ≡ x *> (y <*? z)@
prop_idempotent :: (Eq r, Semiring r) => r -> r -> r -> Bool
prop_idempotent a b c = (a >< b) <> c == a >< (b <> c)


---- Selectivity

-- | If @<>@ is selective then 'ord' defines a total order relation.
prop_selective_total :: (Eq r, Dioid r) => r -> r -> Bool
prop_selective_total a b = prop_selective_additive a b ==> ord a b || ord b a


-- | This is the 'left catch' law for idempotent dioids, e.g:
-- @'pure' a <|> x ≡ 'pure' a@
-- which is equivalent to 
-- @'ord' 'one' ≡ (one ==)
prop_right_absorbative_one :: (Eq r, Monoid r, Semiring r) => r -> Bool
prop_right_absorbative_one r = one <> r == one

-- Given 'prop_right_absorbative_one', 'prop_right_distributive' & 'prop_right_neutral_one'
-- we can derive the following interchange property: @a == a <> b >< a@
prop_interchange :: (Eq r, Monoid r, Semiring r) => r -> r -> Bool
prop_interchange a b =
  prop_right_distributive one a b &&
  prop_right_absorbative_one a &&
  prop_right_neutral_one b ==> a == a <> b >< a

-- See Gondran and Minoux p. 31
prop_left_complete :: (Eq r, Monoid r, Semiring r) => r -> [r] -> Bool
prop_left_complete a bs = a >< fold bs == foldMap (a><) bs

prop_right_complete :: (Eq r, Monoid r, Semiring r) => r -> [r] -> Bool
prop_right_complete a bs = fold bs >< a == foldMap (><a) bs

-------------------------------------------------------------------------------
-- Pre-dioids
-------------------------------------------------------------------------------

-- | 'First a' forms a pre-dioid.
instance (Eq a, Semigroup a) => Dioid (First a) where

  ord = (==)

instance (Eq a, Monoid a) => Dioid (NonEmpty a) where

  ord (a :| as) (b :| bs) = a == b && ord as bs


instance (Eq e, Eq a, Semigroup a) => Dioid (Either e a) where

  Right a `ord` Right b  = a == b
  Right _ `ord` _        = False
  
  Left e  `ord` Left f   = e == f
  Left _  `ord` _        = True


-------------------------------------------------------------------------------
-- Dioids
-------------------------------------------------------------------------------



-- | Only the trivial dioid can have a total order relation that is constantly true.
instance Dioid () where
  ord _ _ = True

-- Note that the partial ordering is distict from the 'Ord' instance. See 'Data.Semiring.Signed'.
instance Dioid Ordering where
  ord GT GT = True
  ord GT EQ = True
  ord GT LT = False

  ord LT LT = True
  ord LT EQ = True
  ord LT GT = False

  ord EQ EQ = True
  ord EQ _  = False


instance Dioid Bool where
  ord = (==>)


instance Dioid Natural where
  ord = (<=)

instance (Dioid a, Dioid b) => Dioid (a, b) where
  ord (a,b) (c, d) = ord a c && ord b d 

instance (Bounded a, Ord a) => Dioid (Max a) where
  ord = (<=)


instance (Bounded a, Ord a) => Dioid (Min a) where
  ord = (>=)


instance (Monoid a, Dioid a) => Dioid (Dual a) where
  ord (Dual a) (Dual b) = ord b a

-- Note that @b@ must be an idempotent?
--instance (Monoid b, Semiring b) => Dioid (a -> b) where
--deriving instance Semiring a => Dioid (Op a b)


instance (Eq r, Monoid r, Semiring r) => Dioid (Under r a) where

  ord = (==)




-- | The free monoid on @a@ is a (right and left-cancellative) dioid. 
--
instance (Eq a, Monoid a) => Dioid [a] where

  ord a b = isJust $ stripPrefix a b





{-
-- natural model for shortest path problems
newtype Path a = Path { runPath :: a } deriving (Eq, Show, Ord, Functor)

-- natural model for maximum capacity path & maximum weight spanning tree problems
newtype Capacity a = Capacity { runCapacity :: a }


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


-- Dioid instances for (R, Min, +) and (N, +, ×)

-- This is a very important class of dioids underlying a wide variety of problems, in particular many non classical path-finding problems in graphs
--instance Dioid End where



--instance Dioid Any where dempty = Any True

-- Note that this instance uses 'False' as its multiplicative unit. 
--instance Dioid All where dempty = All False

--instance Dioid a => Dioid (Maybe a) where  dempty = Just dempty -- relies on a's dempty to satisfy the right absorbtion law

--instance Monoid a => Dioid (Either e a) where dempty = pure mempty


--instance Monad m => Monoid (Kleisli m a)
--instance Monad m => Semigroup (Signed (Kleisli m a) ...


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


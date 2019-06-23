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

import P

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
-- A pre-dioid is a pre-semiring with a (right) canonical order relation relative to '<>':
-- @'ord' a b@ iff @b ≡ a <> c@ for some @c@.
--
-- A dioid is a semiring with the same relation .
class (Eq r, Semiring r) => Dioid r where 
  
  ord :: r -> r -> Bool
  --   ord :: Equivalence r

infix 4 <~

(<~) :: Dioid r => r -> r -> Bool
(<~) = ord




sel :: Dioid r => r -> r -> r
sel a b = bool a b $ ord a b

-- | Monotone pullback to booleans.
ord' :: forall r. (Monoid r, Dioid r) => Equivalence Bool
ord' = contramap fromBoolean (Equivalence ord :: Equivalence r)


infix 4 =~

-- | The equality relation induced by the partial-order structure. It satisfies
-- the laws of an equivalence relation:
-- @
-- Reflexive:  a =~ a
-- Symmetric:  a =~ b ==> b =~ a
-- Transitive: a =~ b && b =~ c ==> a =~ c
-- @
(=~) :: Dioid r => r -> r -> Bool
a =~ b = a `ord` b && b `ord` a


infix 4 <~?

-- | Check whether two elements are ordered with respect to the relation. 
--
-- @
-- x '<~?' y = x '<~' y '||' y '<~' x
-- @
(<~?) :: Dioid r => r -> r -> Bool
a <~? b = a `ord` b || b `ord` a


{-
instance (Dioid a, Selective f) => Semigroup (f a) where 
  f <> g = ifS (liftA2 (<~) f g ) f g 

-}


--prop_idempotent_zero :: Bool
--prop_idempotent_zero  

iff = xnor

------------------------------------------------------------------------------------
-- | Properties of (right) pre-dioids & dioids

-- | 'ord' is a (right) preorder relation relative to '<>'
prop_order_preorder :: (Eq r, Dioid r) => r -> r -> r -> Bool
prop_order_preorder a b c = a `ord` b ==> a <> c == b
 
-- | 'ord' is a total (right) order relation 
prop_order_complete :: (Eq r, Dioid r) => r -> r -> Bool
prop_order_complete a b = (a =~ b) `iff` (a == b)

-- | 'ord' is reflexive (right) order relation 
prop_order_reflexive :: Dioid r => r -> Bool
prop_order_reflexive a = a `ord` a

-- | 'ord' is transitive (right) order relation 
prop_order_transitive :: Dioid r => r -> r -> r -> Bool
prop_order_transitive a b c = a `ord` b && b `ord` c ==> a `ord` c

------------------------------------------------------------------------------------
-- | Properties of dioids

-- | 'fromBoolean' is a Dioid homomorphism (i.e. a monotone or order-preserving function)
prop_monotone_boolean :: forall r. (Monoid r, Dioid r) => Bool -> Bool -> Bool
prop_monotone_boolean a b = a <= b ==> fromBoolean a `ord` (fromBoolean b :: r)

prop_positive_addition :: (Monoid r, Dioid r) => r -> r -> Bool
prop_positive_addition a b = a <> b =~ zero ==> a =~ zero && b =~ zero

-- @a <~ b@ implies @forall x. a >< x <~ b >< x@
prop_order_multiplication :: Dioid r => r -> r -> r -> Bool
prop_order_multiplication a b c = a `ord` b ==> a >< c `ord` (b >< c)

-- @a <~ b@ implies @forall x. x >< a <~ x >< b@
prop_order_multiplication' :: Dioid r => r -> r -> r -> Bool
prop_order_multiplication' a b c = a `ord` b ==> c >< a `ord` (c >< b)

------------------------------------------------------------------------------------
-- | Additional properties of certain subclasses of dioid.


---- Positivity

-- See Gondran and Minoux p. 44 (Exercise 5)
prop_positive_multiplication :: (Dioid r, Monoid r, Semiring r) => r -> r -> Bool
prop_positive_multiplication a b = a >< b =~ zero ==> a =~ zero || b =~ zero

---- Absorbativity

-- | The canonical order relation must be compatible with any additive absorbitivity. 
--
-- This means that a dioid with an absorbative multiplicative unit must satisfy:
--
-- @
-- ('one' <~) ≡ ('one' =~)
-- @
--
prop_absorbative :: (Eq r, Monoid r, Dioid r) => r -> Bool
prop_absorbative r = 
  prop_absorbative_addition one r ==> (one <~ r) `iff` (one =~ r)

---- Idempotency
-- See Gondran and Minoux p. 44 (Exercise 4)

-- | @(a >< b) <> c ≡ a >< (b <> c)@
-- When @r@ is a functor and the semiring structure is derived from 'Selective', 
-- this translates to: @(x *> y) <*? z ≡ x *> (y <*? z)@
prop_idempotent :: (Eq r, Semiring r) => r -> r -> r -> Bool
prop_idempotent a b c = (a >< b) <> c == a >< (b <> c)

---- Commutivity

{-
-- See Gondran and Minoux p. 12
prop_commutative_preorder :: (Eq r, Dioid r) => r -> r -> Bool
prop_commutative_preorder a b c =
  prop_commutative_addition b c ==> 


-- See Gondran and Minoux p. 15 (Proposition 3.4.5)
prop_commutative_order :: (Eq r, Dioid r) => Natural -> r -> r -> r -> Bool
prop_commutative_order n a b c =
  prop_commutative_addition b c &&
  prop_preorder_addition a b c &&
  prop_idempotent_addition n a ==> prop_order_addition_complete b c
-}

---- Selectivity

-- | If @<>@ is selective then 'ord' defines a total order relation.
prop_selective_total :: (Eq r, Dioid r) => r -> r -> Bool
prop_selective_total a b = --prop_selective_additive a b ==> ord a b || ord b a
  prop_selective_addition a b ==> ord a b `xor` ord b a

-- Given 'prop_absorbative_multiplication', 'prop_distributive' & 'prop_neutral_mulitplication'
-- we can derive the following interchange property: @a == a <> b >< a@
prop_interchange :: (Eq r, Monoid r, Semiring r) => r -> r -> Bool
prop_interchange a b =
  prop_distributive one a b &&
  prop_absorbative_multiplication one a &&
  prop_neutral_multiplication one b ==> a == a <> b >< a

-- See Gondran and Minoux p. 31
prop_distributive_complete :: (Eq r, Monoid r, Semiring r) => r -> [r] -> Bool
prop_distributive_complete a bs = fold bs >< a == foldMap (>< a) bs

prop_distributive_complete' :: (Eq r, Monoid r, Semiring r) => r -> [r] -> Bool
prop_distributive_complete' a bs = a >< fold bs == foldMap (a ><) bs


-------------------------------------------------------------------------------
-- Fixed point utilities
-------------------------------------------------------------------------------

-- | Least point of a partially ordered monotone function. Checks that the function is monotone.
lfpFrom :: (Eq a, Dioid a) => a -> (a -> a) -> a
lfpFrom = lfpFrom' ord

-- | Least point of a partially ordered monotone function. Does not checks that the function is monotone.
unsafeLfpFrom :: Eq a => a -> (a -> a) -> a
unsafeLfpFrom = lfpFrom' (\_ _ -> True)

{-# INLINE lfpFrom' #-}
lfpFrom' :: Eq a => (a -> a -> Bool) -> a -> (a -> a) -> a
lfpFrom' check init_x f = go init_x
  where go x | x' == x      = x
             | x `check` x' = go x'
             | otherwise    = error "lfpFrom: non-monotone function"
          where x' = f x


-- | Greatest fixed point of a partially ordered antinone function. Checks that the function is antinone.
{-# INLINE gfpFrom #-}
gfpFrom :: (Eq a, Dioid a) => a -> (a -> a) -> a
gfpFrom = gfpFrom' ord

-- | Greatest fixed point of a partially ordered antinone function. Does not check that the function is antinone.
{-# INLINE unsafeGfpFrom #-}
unsafeGfpFrom :: Eq a => a -> (a -> a) -> a
unsafeGfpFrom = gfpFrom' (\_ _ -> True)

{-# INLINE gfpFrom' #-}
gfpFrom' :: Eq a => (a -> a -> Bool) -> a -> (a -> a) -> a
gfpFrom' check init_x f = go init_x
  where go x | x' == x      = x
             | x' `check` x = go x'
             | otherwise    = error "gfpFrom: non-antinone function"
          where x' = f x

-------------------------------------------------------------------------------
-- Pre-dioids
-------------------------------------------------------------------------------

-- | 'First a' forms a pre-dioid for any semigroup @a@.
instance (Eq a, Semigroup a) => Dioid (First a) where
  ord = (==)


instance Ord a => Dioid (Max a) where
  ord = (<=)


instance Ord a => Dioid (Min a) where
  ord = (>=)


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
  ord = (<=)

instance Dioid Any where
  ord = (<=)

instance Dioid All where
  ord = (<=)

instance Dioid Natural where
  ord = (<=)

instance (Dioid a, Dioid b) => Dioid (a, b) where
  ord (a, b) (c, d) = ord a c && ord b d 

instance (Monoid a, Dioid a) => Dioid (Dual a) where
  ord (Dual a) (Dual b) = ord b a


instance (Monoid r, Dioid r, Semiring r) => Dioid (Over r a) where
  Over a `ord` Over b = a `ord` b

instance (Eq r, Monoid r, Semiring r) => Dioid (Under r a) where
  ord = (==)

{-
ifS (Select ["a"]) (Select ["b"]) (Select ["c"]) *> Select ["d"] *> whenS (Select ["e"]) (Select ["f"])
Select {runSelect = ["a","d","e"]}
Select {runSelect = ["c","d","f"]} -- flipped 'Select' instance

ifS (Dual $ Select ["a"]) (Dual $ Select ["b"]) (Dual $ Select ["c"]) *> (Dual $ Select ["d"]) *> whenS (Dual $ Select ["e"]) (Dual $ Select ["f"])

ifS (Select ["a"]) (Select ["ab"]) (Select ["ac"]) *> Select ["ad"] *> whenS (Select ["de"]) (Select ["df"])

λ>  ifS (Under "a") (Under "b") (Under "c") *> Under "d" *> whenS (Under "e") (Under "f")
-}

newtype Select m a = Select { runSelect :: m }
  deriving (Eq, Functor, Ord, Show)

instance Monoid m => Applicative (Select m) where
  pure _            = Select mempty
  Select x <*> Select y = Select (mappend x y)

instance (Monoid m, Dioid m) => Selective (Select m) where
  select (Select x) (Select y) = Select (y `sel` x)

-- | The free monoid on @a@ is a (right and left-cancellative) dioid. 
--
instance (Eq a, Monoid a) => Dioid [a] where
  ord a b = isJust $ stripPrefix a b







-- instance Dioid (ZipList a) where
--  ord x y = ---- analagous to 'isPrefixOf'


-- Dioid instances for (R, Min, +)

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
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet      as HS
import qualified Data.IntMap       as IM
import qualified Data.IntSet       as IS
import qualified Data.List.Compat  as L
import qualified Data.Map          as M

instance Dioid IS.IntSet where
    ord = IS.isSubsetOf

instance (Eq k, Hashable k) => Dioid (HS.HashSet k) where
    ord a b = HS.null (HS.difference a b)

instance (Ord k, Dioid v) => Dioid (M.Map k v) where
    ord = M.isSubmapOfBy ord

instance Dioid v => Dioid (IM.IntMap v) where
    ord = IM.isSubmapOfBy ord

instance (Eq k, Hashable k, Dioid v) => Dioid (HM.HashMap k v) where
    x `ord` y = {- wish: HM.isSubmapOfBy ord -}
        HM.null (HM.difference x y) && getAll (fold $ HM.intersectionWith (\vx vy -> All (vx `ord` vy)) x y)


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


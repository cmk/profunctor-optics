module Data.Dioid where

import Data.Bool
import Data.Semigroup
import Data.Semiring
import Data.Hemiring
import Data.Monoid hiding (First, Last)
import Numeric.Natural (Natural)

import Data.List (stripPrefix)
import Data.Maybe (isJust)

import qualified Control.Exception as Ex

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

class Hemiring r => Dioid r where 
  
  -- The canonical preorder relation relative to '<>':
  -- 'ord a b' iff 'b == a <> c' for some c.
  ord :: r -> r -> Bool

-- | aka 'left catch' law for idempotent dioids
prop_one_absorb_right :: (Eq r, Dioid r) => r -> Bool
prop_one_absorb_right r = one <> r == one

-- | 'ord' is a preorder relation relative to '<>'
prop_preorder :: (Eq r, Dioid r) => r -> r -> r -> Bool
prop_preorder a b c = bool False True $ ord a b && a <> c == b

-- | The canonical preorder relation relative to addition is a total order relation.
prop_order_total :: (Eq r, Dioid r) => r -> r -> Bool
prop_order_total a b = bool True (a == b) $ ord a b && ord b a 

--instance (Presemiring (f a), Monoid a, Applicative f) => Dioid (f a) where one = pure mempty


-- See Gondran and Minoux p. 44 (Exercise 5)
prop_order_zero :: (Eq r, Dioid r) => r -> r -> Bool
prop_order_zero a b = bool True (a == zero && b == zero) $ a <> b /= zero

-- a ≤ b => forall x. a ⊗ x ≤ b ⊗ x 
--prop_order_compatible :: (Eq r, Dioid r) => r -> r -> Bool


------------------------------------------------------------------------------------
-- Additional (optional) properties for certain subclasses of diads.

{-

Note that left absorbtion (i.e. r <> one == one) is too strong for many instances:

The reason it fails is that we are essentially assuming that any "effects" that x has can be undone once we realize the whole computation is supposed to "fail". Indeed this rule is too strong to make sense for our general notion that MonadPlus provides a notion of choice or addition

https://winterkoninkje.dreamwidth.org/90905.html
-}

prop_one_absorb_left :: (Eq r, Dioid r) => r -> Bool
prop_one_absorb_left r = r <> one == one

-- See Gondran and Minoux p. 44 (Exercise 5)
prop_positive :: (Eq r, Dioid r) => r -> r -> r -> Bool
prop_positive a b c = if a <> b /= zero then True else a == zero || b == zero

-- See Gondran and Minoux p. 44 (Exercise 4)
prop_idempotent :: (Eq r, Dioid r) => r -> r -> r -> Bool
prop_idempotent a b c = (a >< b) <> c == (a <> c) >< (a <> b)



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

instance Dioid Natural where

  ord = (<=)

instance (Bounded a, Ord a) => Dioid (Max a) where

  ord = (<=)


instance (Bounded a, Ord a) => Dioid (Min a) where

  ord = (>=)


instance (Eq a, Monoid a) => Dioid [a] where

  ord a b = isJust $ stripPrefix a b


instance (Monoid e, Monoid a, Dioid e, Dioid a) => Dioid (Either e a) where

  Right a `ord` Right b  = ord a b
  Right _ `ord` _        = False --opposite from Valid
  
  Left e  `ord` Left f   = ord e f
  Left _  `ord` _        = True  --opposite from Valid


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


data Valid e a = Invalid e | Valid a deriving (Show, Eq) --TODO more instances & move to module


instance (Semigroup e, Semigroup a) => Semigroup (Valid e a) where

  Valid a <> Valid b     = Valid $ a <> b

  Valid _ <> Invalid e   = Invalid e

  Invalid e <> Invalid f = Invalid $ e <> f

  Invalid e <> _         = Invalid e 


instance (Semigroup e, Monoid a) => Monoid (Valid e a) where

  mempty = Valid mempty


instance (Semiring e, Semiring a) => Semiring (Valid e a) where

  Valid a >< Valid b     = Valid $ a >< b

  Valid _ >< Invalid e   = Invalid e

  Invalid e >< Invalid f = Invalid $ e >< f

  Invalid e >< _         = Invalid e


instance (Semiring e, Hemiring a) => Hemiring (Valid e a) where

  zero = Valid zero

  one = Valid one


instance (Dioid e, Dioid a) => Dioid (Valid e a) where

  Valid a `ord` Valid b     = ord a b
  Valid _ `ord` _           = True
  
  Invalid e `ord` Invalid f = ord e f
  Invalid _ `ord` _         = False



data Signed a = Zero | Negative a | Positive a | Indeterminate a deriving (Show, Eq)

instance Semigroup a => Semigroup (Signed a) where

  Positive a <> Positive b          = Positive $ a <> b
  Positive a <> Negative b          = Indeterminate $ a <> b
  Positive a <> Zero                = Positive a
  Positive a <> Indeterminate e     = Indeterminate $ a <> e

  Negative a <> Negative b          = Negative $ a <> b
  Negative a <> Positive b          = Indeterminate $ a <> b
  Negative a <> Zero                = Negative a
  Negative a <> Indeterminate e     = Indeterminate $ a <> e

  Zero <> a                       = a

  Indeterminate a <> Positive b          = Indeterminate $ a <> b
  Indeterminate a <> Negative b          = Indeterminate $ a <> b
  Indeterminate a <> Zero                = Indeterminate a
  Indeterminate a <> Indeterminate e     = Indeterminate $ a <> e

instance Semigroup a => Monoid (Signed a) where

  mempty = Zero

{-

instance Monoid a => Semiring (Signed a) where

  zero = mempty

  one = Positive mempty

  Positive >< a = a

  Negative >< Positive            = Negative
  Negative >< Negative            = Positive
  Negative >< Zero                = Zero
  Negative >< Indeterminate       = Indeterminate

  Zero >< _                       = Zero
  Indeterminate >< _              = Indeterminate

  
instance Dioid Signed where

  Positive `ord` Positive         = True
  Positive `ord` Indeterminate    = True
  Positive `ord` _                = False

  Negative `ord` Negative         = True
  Negative `ord` Indeterminate    = True
  Negative `ord` _                = False

  ord Zero       _                = True

  ord Indeterminate Indeterminate = True
  ord Indeterminate _             = False

-}



{- 

+ can be regarded as representing [0, +∞], – as representing [−∞, 0], ? as representing [−∞, +∞], and 0 as representing the set {0}.

? ≥+≥ 0 and ? ≥−≥ 0
instance Ord Sign where
  
  compare 

data Sign = Positive | Negative | Zero | Indeterminate deriving (Show, Eq)

instance Semigroup Sign where

  Positive <> Positive            = Positive
  Positive <> Negative            = Indeterminate
  Positive <> Zero                = Positive
  Positive <> Indeterminate       = Indeterminate

  Negative <> Positive            = Indeterminate
  Negative <> Negative            = Negative
  Negative <> Zero                = Negative
  Negative <> Indeterminate       = Indeterminate

  Zero <> a                       = a

  Indeterminate <> _              = Indeterminate


instance Monoid Sign where

  mempty = Zero

instance Semiring Sign where

  zero = mempty

  one = Positive

  Positive >< a = a

  Negative >< Positive            = Negative
  Negative >< Negative            = Positive
  Negative >< Zero                = Zero
  Negative >< Indeterminate       = Indeterminate

  Zero >< _                       = Zero
  Indeterminate >< _              = Indeterminate

  
instance Dioid Sign where

  Positive `ord` Positive         = True
  Positive `ord` Indeterminate    = True
  Positive `ord` _                = False

  Negative `ord` Negative         = True
  Negative `ord` Indeterminate    = True
  Negative `ord` _                = False

  ord Zero       _                = True

  ord Indeterminate Indeterminate = True
  ord Indeterminate _             = False


-}



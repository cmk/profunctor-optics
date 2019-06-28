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

import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Map.NonEmpty as NEMap
import qualified Data.Sequence as Seq
import qualified Data.Sequence.NonEmpty as NESeq
import qualified Data.Set as Set
import qualified Data.Set.NonEmpty as NESet
import qualified Data.IntMap as IntMap
import qualified Data.IntMap.NonEmpty as NEIntMap

import P

{-
import Control.Monad.Catch (MonadThrow(..))
import Control.Monad.Catch.Pure
import Control.Monad.Fail
-}

infix 4 <~

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
-- A pre-dioid is a pre-semiring with a (right) canonical (<~)er relation relative to '<>':
-- @'<~' a b@ iff @b ≡ a <> c@ for some @c@.
--
-- A dioid is a semiring with the same relation .
class (Eq r, Semiring r) => Dioid r where 

  ord :: r -> r -> Bool

  (<~) :: r -> r -> Bool
  (<~) = ord

  -- monus :: r -> r -> r -- smallest c st a + c = b 
  --TODO only worth refining if this op is going to get used heavily
  --(<~) :: r -> r -> Bool
  --(<~~) :: Eq r => r -> r -> Bool
  --(<~~) a b = lt a b || a == b








sel :: Dioid r => r -> r -> r
sel a b = bool a b $ a <~ b

-- | Monotone pullback to booleans.
ord' :: forall r. (Monoid r, Dioid r) => Equivalence Bool
ord' = contramap fromBoolean (Equivalence (<~) :: Equivalence r)


infix 4 =~

-- | The equality relation induced by the partial-(<~)er structure. It satisfies
-- the laws of an equivalence relation:
-- @
-- Reflexive:  a =~ a
-- Symmetric:  a =~ b ==> b =~ a
-- Transitive: a =~ b && b =~ c ==> a =~ c
-- @
(=~) :: Dioid r => r -> r -> Bool
a =~ b = a <~ b && b <~ a


infix 4 <~?

-- | Check whether two elements are comparable with respect to the relation. 
--
-- @
-- x '<~?' y = x '<~' y '||' y '<~' x
-- @
--
(<~?) :: Dioid r => r -> r -> Bool
a <~? b = a <~ b || b <~ a


{-
instance (Dioid a, Selective f) => Semigroup (f a) where 
  f <> g = ifS (liftA2 (<~) f g ) f g 

-}

-------------------------------------------------------------------------------
-- Fixed points
-------------------------------------------------------------------------------

-- | Implementation of the Kleene fixed-point theorem <http://en.wikipedia.org/wiki/Kleene_fixed-point_theorem>.
-- Forces the function to be monotone.
{-# INLINE lfp #-}
lfp :: (Monoid a, Dioid a) => (a -> a) -> a
lfp = lfpFrom zero

lfpFrom :: Dioid a => a -> (a -> a) -> a
lfpFrom init f = lfpFrom' (<~) init $ \x -> f x <> x

-- | Least point of a partially (<~)ered monotone function. Checks that the function is monotone.
--lfpFrom :: Dioid a => a -> (a -> a) -> a
--lfpFrom = lfpFrom' (<~)

-- | Least point of a partially (<~)ered monotone function. Does not checks that the function is monotone.
unsafeLfpFrom :: Eq a => a -> (a -> a) -> a
unsafeLfpFrom = lfpFrom' (\_ _ -> True)

{-# INLINE lfpFrom' #-}
lfpFrom' :: Eq a => (a -> a -> Bool) -> a -> (a -> a) -> a
lfpFrom' check init_x f = go init_x
  where go x | x' == x      = x
             | x `check` x' = go x'
             | otherwise    = error "lfpFrom: non-monotone function"
          where x' = f x


-------------------------------------------------------------------------------
-- Pre-dioids
-------------------------------------------------------------------------------

-- | 'First a' forms a pre-dioid for any semigroup @a@.
instance (Eq a, Semigroup a) => Dioid (First a) where
  (<~) = (==)


instance Ord a => Dioid (Max a) where
  (<~) = (<=)


instance Ord a => Dioid (Min a) where
  (<~) = (>=)


instance (Eq e, Eq a, Semigroup a) => Dioid (Either e a) where
  Right a <~ Right b  = a == b
  Right _ <~ _        = False
  
  Left e  <~ Left f   = e == f
  Left _  <~ _        = True


instance (Eq a, Monoid a) => Dioid (NonEmpty a) where
  (<~) (a :| as) (b :| bs) = a == b && (<~) as bs

{-
instance Semigroup a => Semiring (NESeq.NESeq a) where
  (><) = liftA2 (<>) 
  {-# INLINE (><) #-}


instance (Ord a, Semigroup a) => Semiring (NESet.NESet a) where
  xs >< ys = foldMap1 (flip NESet.map xs . (<>)) ys
  {-# INLINE (><) #-}


instance (Ord k, Semigroup a) => Semiring (NEMap.NEMap k a) where
  xs >< ys = foldMap1 (flip NEMap.map xs . (<>)) ys
  {-# INLINE (><) #-}


instance Semigroup a => Semiring (NEIntMap.NEIntMap a) where
  xs >< ys = foldMap1 (flip NEIntMap.map xs . (<>)) ys
  {-# INLINE (><) #-}
-}

-------------------------------------------------------------------------------
-- Dioids
-------------------------------------------------------------------------------



-- | Only the trivial dioid can have a total order relation that is constantly true.
instance Dioid () where
  (<~) _ _ = True

-- Note that the partial ordering is derived from the monoid instance, and is distict from the 'Ord' instance. See 'Data.Semiring.Signed'.
instance Dioid Ordering where
  (<~) GT a = (== GT) a

  (<~) LT a = (== LT) a

  (<~) EQ _  = True

instance Dioid Bool where
  (<~) = (<=)

instance Dioid Any where
  (<~) = (<=)

instance Dioid All where
  (<~) = (>=)

instance Dioid Natural where
  (<~) = (<=)

instance Dioid Word where
  (<~) = (<=)

instance (Monoid a, Monoid b, Dioid a, Dioid b) => Dioid (a, b) where
  (<~) (a, b) (c, d) = a <~ c && b <~ d 

-- | The free monoid on @a@ is a (right and left-cancellative) dioid. 
--
instance (Eq a, Monoid a) => Dioid [a] where
  (<~) a b = isJust $ stripPrefix a b

instance (Eq a, Monoid a, Dioid a) => Dioid (Maybe a) where
  Just a <~ Just b = a <~ b
  x@Just{} <~ Nothing = False
  Nothing <~ x = Nothing == x


-- instance Dioid (ZipList a) where
--  (<~) x y = ---- analagous to 'isPrefixOf'

instance (Monoid a, Dioid a) => Dioid (Dual a) where
  (<~) (Dual a) (Dual b) = (<~) b a


instance (Monoid r, Dioid r, Semiring r) => Dioid (Over r a) where
  Over a <~ Over b = a <~ b

instance (Eq r, Monoid r, Semiring r) => Dioid (Under r a) where
  (<~) = (==)

---------------------------------------------------------------------
-- QuickCheck
---------------------------------------------------------------------
{-
import qualified Test.QuickCheck   as QC

instance Semiring QC.Property where
  (<>) = (QC..||.)
  (><) = (QC..&&.)

  zero = QC.property False
  one = QC.property True

instance Dioid QC.Property where
  (<~) = (==)
-}

---------------------------------------------------------------------
--  Instances (containers)
---------------------------------------------------------------------

instance Ord a => Dioid (Set.Set a) where
  (<~) = Set.isSubsetOf

instance (Ord k, Monoid k, Monoid a, Dioid a) => Dioid (Map.Map k a) where
  (<~) = Map.isSubmapOfBy (<~)

instance (Monoid a, Dioid a) => Dioid (IntMap.IntMap a) where
  (<~) = IntMap.isSubmapOfBy (<~)




{-
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet      as HS
import qualified Data.IntMap       as IM
import qualified Data.IntSet       as IS
import qualified Data.List.Compat  as L
import qualified Data.Map          as M

instance Dioid IS.IntSet where
    (<~) = IS.isSubsetOf

instance (Eq k, Hashable k) => Dioid (HS.HashSet k) where
    (<~) a b = HS.null (HS.difference a b)

instance (Eq k, Hashable k, Dioid v) => Dioid (HM.HashMap k v) where
    x <~ y = {- ideally: HM.isSubmapOfBy (<~) -}
        HM.null (HM.difference x y) && getAll (fold $ HM.intersectionWith (\vx vy -> All (vx <~ vy)) x y)

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


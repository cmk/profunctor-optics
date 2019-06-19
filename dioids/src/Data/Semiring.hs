{-# Language ConstrainedClassMethods #-}

module Data.Semiring where

import Control.Applicative
import Data.Monoid hiding (First, Last)
import Data.Semigroup
import Data.Coerce (coerce)
import Numeric.Natural (Natural)

import Data.Functor.Apply
import Data.Semigroup.Foldable.Class as Foldable
import Data.List.NonEmpty (NonEmpty(..))

import Data.Complex (Complex(..))
import Data.Typeable (Typeable)

import GHC.Generics                (Generic, Generic1)
import Foreign.Storable            (Storable)
import Data.Functor.Classes

import           Data.Functor.Contravariant (Predicate(..), Equivalence(..), Op(..))
import           Data.Functor.Identity (Identity(..))

import qualified Data.Foldable as Foldable
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.IntMap.Strict as IntMap

import Control.Selective
import qualified Control.Selective.Free as Free
import qualified Control.Alternative.Free.Final as Free

import P ((==>))

import Control.Monad (ap)
import Orphans ()

--import Data.Functor.Apply
--import Data.Functor.Bind.Class (WrappedApplicative(..))

--http://hackage.haskell.org/package/containers-0.6.0.1/docs/Data-Tree.html#g:1
-- ^ free structure for NearSemirings w/o mult identity


-- If r is a monoid then 'zero' should equal 'zero'.
-- This class does not define a (multiplicative) unit. 
-- Note that while instances should be right distributive, they need not necessarily be left-distributive (e.g. 'End')

{-


[On multiplicative idempotents of a potent semiring](https://www.ncbi.nlm.nih.gov/pmc/articles/PMC534266/pdf/pnas00712-0066.pdf)

[Quasiideals in semirings without zero](https://projecteuclid.org/euclid.pja/1195524783)

In this library, by 'semiring' we mean a semiring without zero (in the 

A semiring is a system consisting of a set S and two binary operations in S
called addition and multiplication such that (a) S together with addition is a
semigroup; (b) S together with multiplication is a semigroup; (c) the left- and
right-hand distributive laws a(b + c) = ab + ac and (b + c)a = ba + ca hold.

a “pre-semiring”, we understand an algebraic structure, consisting of a nonempty
set S with two operations of addition and multiplication such that the following
conditions are satisfied:
(1) (S, +) and (S, ·) are commutative semigroups;
(2) Distributive law: a · (b + c) = a · b + a · c for all a, b, c ∈ S.
The definition of pre-semirings is borrowed from the book [14] and for more on
pre-semirings, one may refer to that.


An algebraic structure that is a pre-semiring and possesses an element that is
a neutral element for its addition and an absorbing element for its multiplication,
is called a hemiring. Usually, the neutral element of a hermring is denoted by 0.
Any hemiring with a multiplicative identity 1 /= 0 is called a semiring. 

 * A Semiring with an additive inverse (-) is a Rng.
 * A Semiring with a multiplicative identity (1) is a Rig.
 * A Semiring with both of those is a Ring.



-}


-- | Pre-semirings and semirings.
-- 
-- A pre-semiring is a type @r@ endowed with two associative binary operations
-- (><) and (<>), along with a right-distributivity property between them:
 
-- @(a <> b) >< c ≡ (a >< c) <> (b >< c)@
--
class Semigroup r => Semiring r where

  -- Multiplicative operation
  (><) :: r -> r -> r  

  -- A semiring homomorphism from the Boolean semiring to @r@. 
  -- If this map is injective then @r@ has a distinct unit.
  fromBoolean :: Monoid r => Bool -> r
  fromBoolean _ = mempty

zero :: (Monoid r, Semiring r) => r           
zero = mempty

-- | Note one may or may not equal zero.
one :: (Monoid r, Semiring r) => r
one = fromBoolean True

fromBooleanDef :: (Monoid r, Semiring r) => r -> Bool -> r
fromBooleanDef _ False = zero
fromBooleanDef o True = o

{-
-- A semiring homomorphism from the natural numbers to @r@.
-- TODO use End instead to avoid n^2 asymptotics
fromNatural :: (Monoid r, Semiring r) => Natural -> r
fromNatural 0 = zero
fromNatural 1 = one
fromNatural n = fromNatural (n - 1) <> one
-}

-- | Cross-multiply two collections.
--
-- >>> cross [1,2,3 ::Int] [1,2,3]
-- 36
--
-- >>> cross [1,2,3 ::Int] []
-- 0
--
cross :: (Foldable t, Applicative t, Monoid r, Semiring r) => t r -> t r -> r
cross a b = Foldable.fold $ liftA2 (><) a b

cross1 :: (Foldable1 t, Apply t, Semiring r) => t r -> t r -> r
cross1 a b = Foldable.fold1 $ liftF2 (><) a b

-- | Fold over a collection using the multiplicative operation of a semiring.
foldMap' :: (Foldable t, Monoid r, Semiring r) => (a -> r) -> t a -> r
foldMap' f = getProd . foldMap (Prod . f)
--foldMap' f = foldr' ((><) . f) one

-- | Fold over a non-empty collection using the multiplicative operation of a semiring.
foldMap1' :: (Foldable1 t, Semiring r) => (a -> r) -> t a -> r
foldMap1' f = getProd . foldMap1 (Prod . f)



--foldSum :: (Monoid r, Semiring r) => (a -> r) -> [a] -> r

--foldSemiring :: (Functor m, Foldable r, Applicative r, Monoid a, Semiring a) => m (r a) -> r a -> m a
--foldSemiring m v = fmap (\r -> Foldable.fold $ liftA2 (><) r v) m


-- Note this function will zero out if there is no multiplicative unit. 
-- For semirings w/o a multiplicative unit use 'foldSemiring'.
foldUnital :: (Monoid r, Semiring r) => (a -> r) -> [[a]] -> r
foldUnital = foldMap . foldMap'
--foldSemiring0 f = foldMap g where g = foldr ((><) . f) one

-- No multiplicative unit.
foldSemiring :: (Monoid r, Semiring r) => (a -> r) -> [NonEmpty a] -> r
foldSemiring = foldMap . foldMap1'

-- No additive or multiplicative unit.
foldPresemiring :: Semiring r => (a -> r) -> NonEmpty (NonEmpty a) -> r
foldPresemiring = foldMap1 . foldMap1'

------------------------------------------------------------------------------------
-- | Properties of pre-semirings

-- | When @r@ is a functor and the semiring structure is derived from 'Alternative', 
-- this translates to: @(f <|> g) <*> a = (f <*> a) <|> (g <*> a)@  
-- See https://en.wikibooks.org/wiki/Haskell/Alternative_and_MonadPlus#Other_suggested_laws

-- When @r@ is a functor and the semiring structure is derived from 'Selective'
prop_right_distributive :: (Eq r, Semiring r) => r -> r -> r -> Bool
prop_right_distributive a b c = (a <> b) >< c == (a >< c) <> (b >< c)

prop_associative_multiplication :: (Eq r, Semiring r) => r -> r -> r -> Bool
prop_associative_multiplication a b c = (a >< b) >< c == a >< (b >< c)

--prop_universal_addition / foldSemiring1

--prop_universal_multiplication


------------------------------------------------------------------------------------
-- | Properties of semirings

-- | When @r@ is a functor and the semiring structure is derived from 'Alternative', 
-- this translates to: @empty <*> a = empty@
-- See https://en.wikibooks.org/wiki/Haskell/Alternative_and_MonadPlus#Other_suggested_laws
prop_right_absorbative_zero :: (Eq r, Monoid r, Semiring r) => r -> Bool
prop_right_absorbative_zero r = zero >< r == zero

prop_right_neutral_one :: (Eq r, Monoid r, Semiring r) => r -> Bool
prop_right_neutral_one r = one >< r == r

prop_left_neutral_one :: (Eq r, Monoid r, Semiring r) => r -> Bool
prop_left_neutral_one r = r >< one == r

prop_right_neutral_zero :: (Eq r, Monoid r, Semiring r) => r -> Bool
prop_right_neutral_zero r = zero <> r == r

prop_left_neutral_zero :: (Eq r, Monoid r, Semiring r) => r -> Bool
prop_left_neutral_zero r = r <> zero == r

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
prop_distinct_zero_one :: forall r. (Eq r, Monoid r, Semiring r) => Bool
prop_distinct_zero_one = zero /= (one :: r)


---- Commutativity

prop_commutative_addition :: (Eq r, Semigroup r) => r -> r -> Bool
prop_commutative_addition a b = a <> b == b <> a

prop_commutative_multiplication :: (Eq r, Semiring r) => r -> r -> Bool
prop_commutative_multiplication a b = a >< b == b >< a


---- Cancellativity

-- It is both right and left-cancellative:
-- m >< m' == m >< m'' ==> m' = m''
-- m' >< m == m'' >< m ==> m' = m''

prop_right_cancellative :: (Eq r, Semiring r) => r -> r -> r -> Bool
prop_right_cancellative a b c = a >< b == a >< c ==> b == c

prop_left_cancellative :: (Eq r, Semiring r) => r -> r -> r -> Bool
prop_left_cancellative a b c = a >< c == b >< c ==> a == c

---- Selectivity

prop_selective_additive :: (Eq r, Semigroup r) => r -> r -> Bool
prop_selective_additive a b = ab == a || ab == b where ab = a <> b

-- A semiring is said to be doubly selective if both operations are selective
prop_selective_multiplicative :: (Eq r, Semiring r) => r -> r -> Bool
prop_selective_multiplicative a b = ab == a || ab == b where ab = a >< b

---- Left 

prop_left_absorbative_zero :: (Eq r, Monoid r, Semiring r) => r -> Bool
prop_left_absorbative_zero r = r >< zero == zero

prop_left_distributive :: (Eq r, Semiring r) => r -> r -> r -> Bool
prop_left_distributive a b c = a >< (b <> c) == (a >< b) <> (a >< c)


-------------------------------------------------------------------------------
-- Pre-semirings
-------------------------------------------------------------------------------

-- | 'First a' forms a pre-semiring.
instance Semigroup a => Semiring (First a) where
  (><) = liftA2 (<>)
  {-# INLINE (><)  #-}


instance Semigroup a => Semiring (Last a) where
  (><) = liftA2 (<>)
  {-# INLINE (><)  #-}


instance Semigroup a => Semiring (NonEmpty a) where

  (><) = liftA2 (<>) 
  {-# INLINE (><)  #-}

--instance (forall a. Semigroup (f a), Semigroup a, Apply f) => Semiring (f a) where (><) = liftF2 (<>)


--instance Semigroup a => Semiring (NE.Set a) where

{-
foo = Sum 2 :| [] :: NonEmpty (Sum Int)
bar = Sum 3 :| [] :: NonEmpty (Sum Int)
baz = Sum 3 :| [] :: NonEmpty (Sum Int)

baz = Sum 4 :| [Sum 4] :: NonEmpty (Sum Int)

prop_zero_absorb_right foo

prop_distrib_right baz foo bar
prop_distrib_right baz bar foo
prop_distrib_right foo bar baz
prop_distrib_right foo baz bar
prop_distrib_right bar foo baz
prop_distrib_right bar baz foo

-}


instance Semigroup a => Semiring (Either e a) where

  (><) = liftA2 (<>)
  {-# INLINE (><)  #-}

  -- fromBoolean = fromBooleanDef $ pure mempty
{-

foo = Right $ Sum 2 :: Either () (Sum Int)
bar = Right $ Sum 3 :: Either () (Sum Int)
baz = Right $ Sum 4 :: Either () (Sum Int)

baz = Left () :: Either () (Sum Int)


prop_distrib_right baz foo bar
prop_distrib_right baz bar foo
prop_distrib_right foo bar baz
prop_distrib_right foo baz bar
prop_distrib_right bar foo baz
prop_distrib_right bar baz foo

instance Alternative Maybe where
    empty = Nothing
    Nothing <|> r = r
    l       <|> _ = l


instance Semigroup (Either a b) where
    Left _ <> b = b
    a      <> _ = a

instance Applicative (Either e) where
    pure          = Right
    Left  e <*> _ = Left e
    Right f <*> r = fmap f r

-}




-------------------------------------------------------------------------------
-- Semirings
-------------------------------------------------------------------------------


instance Semiring () where
  (><) _ _ = ()

  fromBoolean _ = ()


instance Semiring Bool where
  (><) = (&&)

  fromBoolean = id

instance Semiring Natural where
  (><) = (*)

  fromBoolean = fromBooleanDef 1


instance Semiring Int where
  (><) = (*)
  fromBoolean = fromBooleanDef 1

--instance (Semigroup a, Semigroup b) => Semigroup (a, b)

--instance Semigroup Ordering


instance (Monoid b, Semiring b) => Semiring (a -> b) where
  (><) f g = \x -> f x >< g x
  {-# INLINE (><)  #-}

  fromBoolean = const . fromBoolean

--instance (Monoid b, Semiring b) => Semiring (Op a b) where



instance Monoid a => Semiring [a] where 

  (><) = liftA2 (<>)
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ pure mempty

{-
foo = [WrappedNum 2] :: [WrappedNum Int]
bar = [WrappedNum 1, WrappedNum 3] :: [WrappedNum Int]
baz = [WrappedNum 2, WrappedNum 3] :: [WrappedNum Int]

prop_zero_absorb_right foo

prop_distrib_right baz foo bar
prop_distrib_right baz bar foo
prop_distrib_right foo bar baz
prop_distrib_right foo baz bar
prop_distrib_right bar foo baz
prop_distrib_right bar baz foo
-}


instance (Monoid a, Semiring a) => Semiring (Maybe a) where 

  (><) = liftA2 (><)
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ pure mempty

{-


foo = Just $ WrappedNum 2 :: Maybe (WrappedNum Int)
bar = Just $ WrappedNum 3 :: Maybe (WrappedNum Int)
baz = Just $ WrappedNum 4 :: Maybe (WrappedNum Int)
d = Nothing :: Maybe (WrappedNum Int)
dempty
c = Just $ WrappedNum 0 :: Maybe (WrappedNum Int)

prop_distrib_right baz foo bar
prop_distrib_right baz bar foo
prop_distrib_right foo bar baz
prop_distrib_right foo baz bar
prop_distrib_right bar foo baz
prop_distrib_right bar baz foo


instance Alternative Maybe where
    empty = Nothing
    Nothing <|> r = r
    l       <|> _ = l

instance Semigroup a => Semigroup (Maybe a) where
    Nothing <> b       = b
    a       <> Nothing = a
    Just a  <> Just b  = Just (a <> b)

    stimes = stimesMaybe
-}





instance (Bounded a, Ord a) => Semiring (Max a) where
  (><) = min
  {-# INLINE (><)  #-}

  fromBoolean = fromBooleanDef maxBound

instance (Bounded a, Ord a) => Semiring (Min a) where
  (><) = max
  {-# INLINE (><)  #-}

  fromBoolean = fromBooleanDef minBound


{-

foo = Max 2 :: Max Int
bar = Max 3 :: Max Int
baz = Max 1 :: Max Int

foo = Min 2 :: Min Int
bar = Min 3 :: Min Int
baz = Min 1 :: Min Int

foldSemiring1 id $ ( foo :| [bar]) :| [bar :| [baz]] -- 1
foldSemiring id [ foo :| [bar], bar :| [baz]] -- 1
foldSemiring01 id [[foo, bar], [bar, baz], [baz], []] -- -9223372036854775808

foldSemiring01 id [[bar, foo]]
prop_zero_absorb_right foo
prop_zero_ident_right foo
prop_one_ident_right foo

prop_distrib_right baz foo bar
prop_distrib_right baz bar foo
prop_distrib_right foo bar baz
prop_distrib_right foo baz bar
prop_distrib_right bar foo baz
prop_distrib_right bar baz foo
-}

instance (Monoid a, Semiring a) => Semiring (Dual a) where
  (><) = liftA2 (><)
  {-# INLINE (><)  #-}

  fromBoolean = Dual . fromBoolean
  {-# INLINE fromBoolean #-}


instance (Monoid a, Semiring a) => Semiring (Const a b) where

  (Const x) >< (Const y) = Const (x >< y)
  {-# INLINE (><)  #-}

  fromBoolean = Const . fromBoolean
  {-# INLINE fromBoolean #-}

instance (Monoid a, Semiring a) => Semiring (Identity a) where

  (><) = liftA2 (><)
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ pure mempty


instance (Monoid r, Semiring r) => Semiring (Over r a) where

  Over x >< Over y = Over (x >< y)
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ Over mempty

-- ord (Over a) (Over b) = ord a b


instance (Monoid r, Semiring r) => Semiring (Under r a) where

  Under x >< Under y = Under (x >< y)
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ Under mempty

-- ord (Under a) (Under b) = ord a b

{-
-- | This instance can suffer due to floating point arithmetic.
instance Ring a => Semiring (Complex a) where
  --(x :+ y) >< (x' :+ y') = (x >< x' - (y >< y')) :+ (x >< y' + y >< x')

  (><) = liftA2 (><)
  {-# INLINE (><)  #-}

  fromBoolean n = fromBoolean n :+ zero
  {-# INLINE fromBoolean #-}
-}


instance Semiring Any where 

  (><) = coerce (&&)
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ Any True

-- Note that this instance uses 'False' as its multiplicative unit. 
instance Semiring All where 

  (><) = coerce (||)
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ All False


--instance (forall a. Semigroup (f a), Semigroup a, Apply f) => Semiring (f a) where (><) = liftF2 (<>)



instance Monoid a => Semiring (Free.Alt f a) where

  (><) = liftA2 (<>)
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ pure mempty

-- Note: if 'Alternative' is ever refactored to fix the left distribution law issue then 'Alt' should be updated here as well.
instance (Monoid a, Alternative f) => Semiring (Alt f a) where

  (><) = liftA2 (<>)
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ pure mempty


-- Note: this instance uses the 'Applicative' monoid as the underlying semigroup.
-- Note: this instance should only be used with 'Applicative's that have no 'Alternative' instance
-- as it provides a 'Monoid' instance based on 'pure zero'.
instance (Semiring a, Applicative f) => Semiring (Ap f a) where 

  (><) = liftA2 (><)
  {-# INLINE (><) #-}

  --fromBoolean = fromBooleanDef $ pure mempty

instance Semiring a => Semiring (IO a) where 

  (><) = liftA2 (><)
  {-# INLINE (><) #-}

  --fromBoolean = fromBooleanDef $ pure mempty


-- | Translate between semiring ops and Applicative / Alternative ops. 
-- >>> Semi 2 <|> Semi (3::Int)
-- Semi {getSemi = 5}
newtype Semi a b = Semi { getSemi :: a }
  deriving (Eq,Ord,Show,Bounded,Generic,Generic1,Typeable,Storable,Functor)

{-

instance Eq1 Semi where
  liftEq = coerce
  {-# INLINE liftEq #-}

instance Ord1 Semi where
  liftCompare = coerce
  {-# INLINE liftCompare #-}

instance Show1 Mul where
  liftShowsPrec = showsNewtype "Mul" "getMul"
  {-# INLINE liftShowsPrec #-}
-}

instance Semigroup a => Semigroup (Semi a b) where
  Semi a <> Semi b = Semi (a <> b)
  {-# INLINE (<>) #-}

-- Note that 'one' must be distinct from 'zero' for this instance to be legal.
instance Monoid a => Monoid (Semi a b) where
  mempty = Semi mempty
  {-# INLINE mempty #-}

instance (Monoid a, Semiring a) => Applicative (Semi a) where
  pure = const (Semi one)
  Semi a <*> Semi b = Semi (a >< b)

instance (Monoid a, Semiring a) => Alternative (Semi a) where 
  empty = Semi zero

  Semi a <|> Semi b = Semi (a <> b)






-- | Monoid under '><'. Analogous to 'Data.Monoid.Product', but uses the
-- 'Semiring' constraint, rather than 'Num'.
newtype Prod a = Prod { getProd :: a }
  deriving (Eq,Ord,Show,Bounded,Generic,Generic1,Typeable,Storable,Functor)

instance Applicative Prod where
  pure = Prod
  Prod f <*> Prod a = Prod (f a)

instance Eq1 Prod where
  liftEq = coerce
  {-# INLINE liftEq #-}

instance Ord1 Prod where
  liftCompare = coerce
  {-# INLINE liftCompare #-}

{-
instance Show1 Mul where
  liftShowsPrec = showsNewtype "Mul" "getMul"
  {-# INLINE liftShowsPrec #-}
-}

instance Semiring a => Semigroup (Prod a) where
  (<>) = liftA2 (><)
  {-# INLINE (<>) #-}

-- Note that 'one' must be distinct from 'zero' for this instance to be legal.
instance (Monoid a, Semiring a) => Monoid (Prod a) where
  mempty = Prod one
  {-# INLINE mempty #-}


---------------------------------------------------------------------
--  Instances (contravariant)
---------------------------------------------------------------------

--deriving instance Semiring (Predicate a)

--deriving instance Semiring a => Semiring (Equivalence a)

--deriving instance Semiring a => Semiring (Op a b)



---------------------------------------------------------------------
--  Instances (containers)
---------------------------------------------------------------------


--TODO nonempty instances
instance (Ord a, Monoid a) => Semiring (Set.Set a) where

  xs >< ys = Foldable.foldMap (flip Set.map xs . (<>)) ys
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ Set.singleton mempty

instance (Ord k, Monoid k, Monoid a) => Semiring (Map.Map k a) where

  xs >< ys = Foldable.foldMap (flip Map.map xs . (<>)) ys
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ Map.singleton mempty mempty

-- http://hackage.haskell.org/package/nonempty-containers-0.2.0.0/docs/Data-IntMap-NonEmpty.html
instance Monoid a => Semiring (IntMap.IntMap a) where

  xs >< ys = Foldable.foldMap (flip IntMap.map xs . (<>)) ys
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ IntMap.singleton 0 mempty


{-

foo = IntMap.fromList [(1,Sum (1 :: Int)), (3, Sum 2)]
bar = IntMap.fromList [(1,Sum (1 :: Int)), (2, Sum 2)]
baz = IntMap.fromList [(2,Sum (1 :: Int)), (3, Sum 2)]

foo = Map.fromList [("hi",Sum (1 :: Int)), ("there", Sum 2)]
bar = Map.fromList [("hi",Sum (1 :: Int)), ("you", Sum 2)]
baz = Map.fromList [("you",Sum (1 :: Int)), ("there", Sum 2)]

prop_zero_absorb_right baz

prop_distrib_right baz foo bar
prop_distrib_right baz bar foo
prop_distrib_right foo bar baz
prop_distrib_right foo baz bar
prop_distrib_right bar foo baz
prop_distrib_right bar baz foo

prop_distrib_left baz foo bar 
prop_distrib_left baz bar foo
prop_distrib_left foo bar baz
prop_distrib_left foo baz bar -- False!
prop_distrib_left bar foo baz
prop_distrib_left bar baz foo -- False!


foo >< (bar <> baz) == (foo >< bar) <> (foo >< baz)

rhs = bar >< (foo <> baz) 
lhs = (bar >< foo) <> (bar >< baz)

λ> rhs
fromList [("hi",Sum {getSum = 2}),("there",Sum {getSum = 3}),("you",Sum {getSum = 3})]
λ> lhs
fromList [("hi",Sum {getSum = 2}),("there",Sum {getSum = 3}),("you",Sum {getSum = 3})]
-}





-- A wrapper for 'Map' that implements a non-destructive addition.
newtype WrappedMap k a = WrappedMap { unWrappedMap :: Map.Map k a } deriving ( Eq , Ord , Show )


instance (Ord k, Semigroup a) => Semigroup (WrappedMap k a) where

  (WrappedMap xs) <> (WrappedMap ys) = WrappedMap $ Map.unionWith (<>) xs ys


instance (Ord k, Semigroup a) => Monoid (WrappedMap k a) where

  mempty = WrappedMap Map.empty

-- This semiring has both right and left distributivity.
instance (Ord k, Semigroup k, Semiring a) => Semiring (WrappedMap k a) where

  (WrappedMap xs) >< (WrappedMap ys) = WrappedMap $ Map.fromListWith (<>) 
     [ (k <> l, v >< u) | (k, v) <- Map.toList xs, (l, u) <- Map.toList ys ]
  {-# INLINE (><) #-}

  --fromBoolean = fromBooleanDef $ WrappedMap (Map.singleton mempty one)


{-
λ> foo = Map.fromList [("hi",WrappedNum (1 :: Int)), ("there", WrappedNum 2)]
λ> bar = Map.fromList [("hi",WrappedNum (1 :: Int)), ("you", WrappedNum 2)]
λ> foo >< bar

foo = WrappedMap $ Map.fromList [("hi",WrappedNum (1 :: Int)), ("there", WrappedNum 2)]
bar = WrappedMap $ Map.fromList [("hi",WrappedNum (1 :: Int)), ("you", WrappedNum 2)]
baz = WrappedMap $ Map.fromList [("you",WrappedNum (1 :: Int)), ("there", WrappedNum 2)]

prop_zero_absorb_right baz

prop_distrib_right baz foo bar
prop_distrib_right baz bar foo
prop_distrib_right foo bar baz
prop_distrib_right foo baz bar
prop_distrib_right bar foo baz
prop_distrib_right bar baz foo
-}







{-
Deriving Semiring via First
Deriving Semiring via Sum
Deriving Semiring via Any
Deriving Semiring via All



foldMap :: (Foldable t, Monoid m) => (a -> m) -> t a -> m
toList :: Foldable t => t a -> [a]

productWith1
productWith1 :: (Foldable1 f, Multiplicative r) => (a -> r) -> f a -> r

foldMap1 :: (Foldable1 t, Semigroup m) => (a -> m) -> t a -> m
toNonEmpty :: Foldable1 t => t a -> NonEmpty a

sumOf :: (Foldable t, Dioid m) => (a -> m) -> t a -> m
productOf :: (Foldable t, Dioid m) => (a -> m) -> t a -> m

toMaybe :: Foldable t => t a -> Maybe a

-- | One or none. Leaves the additive zero out.
optional :: (Alt f, Applicative f) => f a -> f (Maybe a)
optional v = Just <$> v <!> pure Nothing

sumOf :: (Foldable t, Semiring m) => (a -> m) -> t a -> m
productOf :: (Foldable1 t, Semiring m) => (a -> m) -> t a -> m

-- @Foldable@ instances are expected to satisfy the following laws:
--
-- > foldr f z t = appEndo (foldMap (Endo . f) t ) z
--
-- > foldl f z t = appEndo (getDual (foldMap (Dual . Endo . flip f) t)) z
--
-- > fold = foldMap id
--
-- > length = getSum . foldMap (Sum . const  1)
--
-- @sum@, @product@, @maximum@, and @minimum@ should all be essentially
-- equivalent to @foldMap@ forms, such as
--
-- > sum = getSum . foldMap Sum
--
-- but may be less defined.
--
-- If the type is also a 'Functor' instance, it should satisfy
--
-- > foldMap f = fold . fmap f
--
-- which implies that
--
-- > foldMap f . fmap g = foldMap (f . g)

class Foldable t where
    {-# MINIMAL foldMap | foldr #-}

    -- | Combine the elements of a structure using a monoid.
    fold :: Monoid m => t m -> m
    fold = foldMap id

    -- | Map each element of the structure to a monoid,
    -- and combine the results.
    foldMap :: Monoid m => (a -> m) -> t a -> m
    {-# INLINE foldMap #-}
    -- This INLINE allows more list functions to fuse. See Trac #9848.
    foldMap f = foldr (mappend . f) mempty

class Foldable t => Foldable1 t where
  fold1 :: Semigroup m => t m -> m
  foldMap1 :: Semigroup m => (a -> m) -> t a -> m
  toNonEmpty :: t a -> NonEmpty a

  foldMap1 f = maybe (error "foldMap1") id . getOption . foldMap (Option . Just . f)
  fold1 = foldMap1 id
  toNonEmpty = foldMap1 (:|[])


-}





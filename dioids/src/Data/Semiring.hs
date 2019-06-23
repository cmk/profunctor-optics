{-# Language ConstrainedClassMethods #-}

module Data.Semiring where

import Control.Applicative
import Data.Monoid (Alt(..),Ap(..)) --hiding (First(..), Last(..))
import Data.Semigroup
import Data.Coerce (coerce)
import Numeric.Natural (Natural)

import Data.Functor.Apply
import Data.Functor.Contravariant.Divisible
import Data.Functor.Contravariant
import Data.Semigroup.Foldable.Class as Foldable
import Data.List.NonEmpty (NonEmpty(..))

import Data.Complex (Complex(..))
import Data.Typeable (Typeable)

import GHC.Real (even)
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

import P

import Control.Monad (ap)
import Orphans ()



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


-- | Fold over a collection using the multiplicative operation of a semiring.
-- 
-- @
-- 'foldMap'' f ≡ 'Data.Foldable.foldr'' ((><) . f) 'one'
-- @
--
-- >>> (foldMap . foldMap') id [[1, 2], [3, (4 :: Int)]] -- 1 >< 2 <> 3 >< 4
-- 14
--
-- >>> (foldMap' . foldMap) id [[1, 2], [3, (4 :: Int)]] -- 1 <> 2 >< 3 <> 4
-- 21
--
-- See also 'Data.Semiring.Endomorphism.productWith'.
--
-- For semirings without a distinct multiplicative unit this is equivalent to @const zero@:
--
-- >>> foldMap' Just [1..(5 :: Int)]
-- Just 0
--
-- In this situation you most likely want to use 'foldMap1''.
--
foldMap' :: (Foldable t, Monoid r, Semiring r) => (a -> r) -> t a -> r
foldMap' f = foldr' ((><) . f) one


-- | Fold over a non-empty collection using the multiplicative operation of a semiring.
--
--
--
-- As the collection is non-empty this does not require a distinct multiplicative unit:
--
-- >>> foldMap1' Just $ 1 :| [2..(5 :: Int)]
-- Just 120
--
foldMap1' :: (Foldable1 t, Semiring r) => (a -> r) -> t a -> r
foldMap1' f = getProd . foldMap1 (Prod . f)

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

-- >>> cross1 (Right 2 :| [Left "oops"]) (Right 2 :| [Right 3]) :: Either [Char] Int
-- Right 4
cross1 :: (Foldable1 t, Apply t, Semiring r) => t r -> t r -> r
cross1 a b = Foldable.fold1 $ liftF2 (><) a b

rep :: Monoid m => m -> Natural -> m
rep x = go
  where
    go 0 = mempty
    go 1 = x
    go n
      | even n = r <> r
      | otherwise = x <> r <> r
      where
        r = go (n `div` 2)
{-# INLINE rep #-}

------------------------------------------------------------------------------------
-- | Properties of pre-semirings & semirings.

-- | When @r@ is a functor and the semiring structure is derived from 'Alternative', 
-- this translates to: @(f <|> g) <*> a = (f <*> a) <|> (g <*> a)@  
-- See https://en.wikibooks.org/wiki/Haskell/Alternative_and_MonadPlus#Other_suggested_laws

-- When @r@ is a functor and the semiring structure is derived from 'Selective'
prop_distributive :: (Eq r, Semiring r) => r -> r -> r -> Bool
prop_distributive a b c = (a <> b) >< c == (a >< c) <> (b >< c)

prop_associative_multiplication :: (Eq r, Semiring r) => r -> r -> r -> Bool
prop_associative_multiplication a b c = (a >< b) >< c == a >< (b >< c)

--prop_universal_addition / foldSemiring1

--prop_universal_multiplication


------------------------------------------------------------------------------------
-- | Properties of semirings


-- | A pre-semiring with a (right) absorbative addititive unit must satisfy:
--
-- @
-- 'prop_absorbative_multiplcation' 'zero' ≡ const True
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
prop_absorbative_multiplication :: (Eq r, Semiring r) => r -> r -> Bool
prop_absorbative_multiplication o r = o >< r == o

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

---- Neutrality.

-- | A pre-semiring with a (right) neutral multiplicative unit must satisfy:
--
-- @
-- 'prop_neutral_multiplcation' 'one' ≡ const True
-- @
-- 
-- All (right) semirings must have a (right) neutral multiplicative unit.
-- 
prop_neutral_multiplication :: (Eq r, Semiring r) => r -> r -> Bool
prop_neutral_multiplication o r = o >< r == r

-- | Left multiplicative neutrality of 'zero' and/or 'one'.
prop_neutral_multiplication' :: (Eq r, Semiring r) => r -> r -> Bool
prop_neutral_multiplication' o r = r >< o == r


------------------------------------------------------------------------------------
-- | Additional (optional) properties of certain subclasses of 'Semiring'.

-- | The existence of distinguished additive and multiplicative units distinguishes 
-- a semiring (resp. dioid) from a pre-semiring (pre-dioid).
prop_unital :: (Eq r, Monoid r, Semiring r) => r -> Bool
prop_unital o = zero /= o


---- Absorbativity

-- A semiring with a (right) absorbative muliplicative unit must satisfy:
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
prop_absorbative_addition :: (Eq r, Semiring r) => r -> r -> Bool
prop_absorbative_addition o r = o <> r == o



-- A semiring with a (left) absorbative muliplicative unit must satisfy:
--
-- @
-- r <> 'one' ≡ 'one'
-- @
--
-- Note that the left absorbtion property is too strong for many instances. 
-- This is because it requires that any effects that @r@ has can be undone.
-- See https://winterkoninkje.dreamwidth.org/90905.html
--
prop_absorbative_addition' :: (Eq r, Semiring r) => r -> r -> Bool
prop_absorbative_addition' o r = r <> o == o


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


---- Commutativity

prop_commutative_addition :: (Eq r, Semigroup r) => r -> r -> Bool
prop_commutative_addition a b = a <> b == b <> a

prop_commutative_multiplication :: (Eq r, Semiring r) => r -> r -> Bool
prop_commutative_multiplication a b = a >< b == b >< a

---- Left-handed versions of some common properties.

prop_distributive' :: (Eq r, Semiring r) => r -> r -> r -> Bool
prop_distributive' a b c = a >< (b <> c) == (a >< b) <> (a >< c)

prop_absorbative_multiplication' :: (Eq r, Semiring r) => r -> r -> Bool
prop_absorbative_multiplication' o r = r >< o == o


---- Idempotency

-- G & M p. 15, Proposition 3.4.5 .
prop_idempotent_addition :: (Eq r, Semigroup r) => Natural -> r -> Bool
prop_idempotent_addition n r = n >= 1 ==> r == foldMap1 id (r :| rep [r] (n-1))


---- Completeness

-------------------------------------------------------------------------------
-- Pre-semirings
-------------------------------------------------------------------------------

-- | 'First a' forms a pre-semiring for any semigroup @a@.
--
-- >>> foldMap1 First $ 1 :| [2..(5 :: Int)] >< 1 :| [2..(5 :: Int)]
-- First {getFirst = 1}
--
-- >>> foldMap1' First $ 1 :| [2..(5 :: Int)]
-- First {getFirst = 15}
--
-- >>> foldMap1 First $ Nothing :| [Just (5 :: Int), Just 6,  Nothing]
-- First {getFirst = Nothing}
--
-- >>> foldMap1' First $ Nothing :| [Just (5 :: Int), Just 6,  Nothing]
-- First {getFirst = Just 11}
--
instance Semigroup a => Semiring (First a) where
  (><) = liftF2 (<>)
  {-# INLINE (><)  #-}


instance Semigroup a => Semiring (Last a) where
  (><) = liftF2 (<>)
  {-# INLINE (><)  #-}

instance Ord a => Semiring (Max a) where
  (><) = min
  {-# INLINE (><)  #-}


instance Ord a => Semiring (Min a) where
  (><) = max
  {-# INLINE (><)  #-}


-- See also 'Data.Dioid.Warning' and 'Data.Dioid.Valid'.
-- >>> (1 :| [2 :: Int]) >< (3 :| [4 :: Int])
-- 4 :| [5,5,6]
instance Semigroup a => Semiring (NonEmpty a) where

  (><) = liftF2 (<>) 
  {-# INLINE (><)  #-}


instance Semigroup a => Semiring (Either e a) where

  (><) = liftF2 (<>)
  {-# INLINE (><)  #-}


--instance Semigroup a => Semiring (NE.Set a) where

-------------------------------------------------------------------------------
-- Semirings
-------------------------------------------------------------------------------


instance Semiring () where
  (><) _ _ = ()
  fromBoolean _ = ()

-- See also 'Data.Semiring.Sign'.
instance Semiring Ordering where
  LT >< LT = LT
  LT >< GT = LT
  _  >< EQ = EQ
  EQ >< _  = EQ
  GT >< x  = x

  fromBoolean = fromBooleanDef GT

instance Semiring Bool where
  (><) = (&&)
  fromBoolean = id


instance Semiring Natural where
  (><) = (*)
  fromBoolean = fromBooleanDef 1


instance Semiring Int where
  (><) = (*)
  fromBoolean = fromBooleanDef 1


instance (Semiring a, Semiring b) => Semiring (a, b) where
  (a,b) >< (c, d) = (a><c, b><d)
  {-# INLINE (><) #-}

  --fromBoolean b = (fromBoolean b, fromBoolean b)

-- >>> (> (0::Int)) >< ((< 10) <> (== 15)) $ 10
-- False
-- >>> (> (0::Int)) >< ((< 10) <> (== 15)) $ 15
-- True
instance (Monoid b, Semiring b) => Semiring (a -> b) where
  (><) = liftA2 (><)
  {-# INLINE (><) #-}

  fromBoolean = const . fromBoolean

instance (Monoid a, Semiring a) => Semiring (Op a b) where
  Op f >< Op g = Op $ \x -> f x >< g x
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ Op (const one)


--TODO use Monoid instances here or no?
instance Monoid a => Semiring [a] where 
  (><) = liftA2 (<>)
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ pure mempty


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








instance (Monoid a, Semiring a) => Semiring (Dual a) where
  (><) = liftA2 $ flip (><)
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

-- Note that this instance uses 'All False' as its multiplicative unit. 
instance Semiring All where 
  (><) = coerce (||)
  {-# INLINE (><) #-}

  --Note that the truth values are flipped here to create a
  --valid semiring homomorphism. Users should precompose with 'not'
  --where necessary. 
  fromBoolean False = All True
  fromBoolean True = All False


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





---------------------------------------------------------------------
--  Instances (contravariant)
---------------------------------------------------------------------


-- Note that due to the underlying 'Monoid' instance this instance
-- has 'All' semiring semantics rather than 'Any'.
instance Semiring (Predicate a) where
  Predicate f >< Predicate g = Predicate $ \x -> f x || g x
  {-# INLINE (><) #-}

  --Note that the truth values are flipped here to create a
  --valid semiring homomorphism. Users should precompose with 'not'
  --where necessary. 
  fromBoolean False = Predicate $ const True
  fromBoolean True = Predicate $ const False


-- Note that due to the underlying 'Monoid' instance this instance
-- has 'All' semiring semantics rather than 'Any'.
instance Semiring (Equivalence a) where
  Equivalence f >< Equivalence g = Equivalence $ \x y -> f x y || g x y
  {-# INLINE (><) #-}

  --Note that the truth values are flipped here to create a
  --valid semiring homomorphism. Users should precompose with 'not'
  --where necessary. 
  fromBoolean False = Equivalence $ \_ _ -> True
  fromBoolean True = Equivalence $ \_ _ -> False


instance Semiring (Comparison a) where
  Comparison f >< Comparison g = Comparison $ \x y -> f x y >< g x y
  {-# INLINE (><) #-}

  --Note that the truth values are flipped here to create a
  --valid semiring homomorphism. Users should precompose with 'not'
  --where necessary. 
  fromBoolean = fromBooleanDef $ Comparison $ \_ _ -> GT


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


---------------------------------------------------------------------
-- Newtypes
---------------------------------------------------------------------

{-
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
-}





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




-- Provide a 'Num' instance for a 'Semiring' (or 'Dioid') in which negation has no effect.
newtype Number a = Number { unNumber :: a }
  deriving (Eq,Ord,Show,Bounded,Generic,Generic1,Typeable,Storable,Functor)


instance Semigroup r => Semigroup (Number r) where
  (<>) = liftA2 (<>)
  {-# INLINE (<>) #-}


instance Monoid r => Monoid (Number r) where
  mempty = Number mempty
  {-# INLINE mempty #-}

instance (Monoid r, Semiring r) => Semiring (Number r) where
  (><) = liftA2 (><)
  fromBoolean = Number . fromBoolean

instance Applicative Number where
  pure = Number
  Number f <*> Number a = Number $ f a

-- Note that 'one' must be distinct from 'zero' for this instance to be legal.
instance (Monoid r, Semiring r) => Num (Number r) where
  (+) = liftA2 (<>)
  (*) = liftA2 (><)
  negate = id
  abs = id
  signum zero = zero
  signum _ = one
  fromInteger 0 = zero
  fromInteger 1 = one
  fromInteger x = fromInteger (abs x - 1) <> one --TODO improve



-- | Provide the correct Semigroup, Monoid, Semiring, & Ring instances for an arbitrary Num. 
-- Used with GHC 8.6+'s DerivingVia extension.
newtype WrappedNum a = WrappedNum { unWrappedNum :: a } deriving (Eq, Show, Num, Ord, Functor)
{-
  deriving
    ( Eq
    , Foldable
    , Fractional
    , Functor
    , Generic
    , Generic1
    , Num
    , Ord
    , Real
    , RealFrac
    , Show
    , Storable
    , Traversable
    , Typeable
    )
-}

instance Num a => Semigroup (WrappedNum a) where

  (<>) = (+)


instance Num a => Monoid (WrappedNum a) where

  mempty = 0


instance Num a => Semiring (WrappedNum a) where

  (><) = (*)
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef 1


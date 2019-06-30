{-# Language ConstrainedClassMethods #-}

module Data.Semiring where

import Control.Applicative (Const(..))
import Control.Monad (ap)
import Data.Monoid (Alt(..),Ap(..))
import Data.Coerce (coerce)

import Data.Functor.Apply
import Data.Functor.Contravariant.Divisible
import Data.Functor.Contravariant
import Data.List (unfoldr)
import Data.List.NonEmpty (NonEmpty(..))

import Data.Complex (Complex(..))
import Data.Typeable (Typeable)
import Data.Validity
import Data.Validity.Map
import Data.GenValidity
import Data.GenValidity.Map

import GHC.Real (even)
import GHC.Generics                (Generic, Generic1)
import Foreign.Storable            (Storable)
import Data.Functor.Classes

import Data.Functor.Contravariant (Predicate(..), Equivalence(..), Op(..))
import Data.Functor.Identity (Identity(..))

import P
import Orphans ()

import qualified Control.Alternative.Free.Final as Free

import qualified Data.Map as Map
import qualified Data.Map.NonEmpty as NEMap
import qualified Data.Sequence as Seq
import qualified Data.Sequence.NonEmpty as NESeq
import qualified Data.Set as Set
import qualified Data.Set.NonEmpty as NESet
import qualified Data.IntMap as IntMap
import qualified Data.IntMap.NonEmpty as NEIntMap


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


-- | Right pre-semirings and semirings.
-- 
-- A right pre-semiring is a type /R/ endowed with two associative binary 
-- (i.e. semigroup) operations: (<>) and (><), along with a right-distributivity 
-- property connecting them:
--
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

-- | Note 'Semiring' does not require that 'one' be distinct from 'zero'.
one :: (Monoid r, Semiring r) => r
one = fromBoolean True

fromBooleanDef :: (Monoid r, Semiring r) => r -> Bool -> r
fromBooleanDef _ False = zero
fromBooleanDef o True = o


-- | Fold over a collection using the multiplicative operation of a semiring.
-- 
-- @
-- 'foldMap'' f ≡ 'Data.foldr'' ((><) . f) 'one'
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
cross a b = fold $ liftA2 (><) a b

-- >>> cross1 (Right 2 :| [Left "oops"]) (Right 2 :| [Right 3]) :: Either [Char] Int
-- Right 4
cross1 :: (Foldable1 t, Apply t, Semiring r) => t r -> t r -> r
cross1 a b = fold1 $ liftF2 (><) a b


infixr 8 ^

(^) :: (Monoid r, Semiring r) => r -> Natural -> r
(^) x = go
  where
    go 0 = one
    go 1 = x
    go n
      | even n = r >< r
      | otherwise = x >< r >< r
      where
        r = go (n `div` 2)
{-# INLINE (^) #-}

rep :: Monoid r => r -> Natural -> r
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

powers :: (Monoid r, Semiring r) => Natural -> r -> r
powers n a = foldr' (<>) one . flip unfoldr n $ \m -> 
  if m == 0 then Nothing else Just (a^m,m-1)

-------------------------------------------------------------------------------
-- 'Closed'
-------------------------------------------------------------------------------

-- | A <https://en.wikipedia.org/wiki/Semiring#Closed_semirings closed semiring>
-- adds one operation, 'star' to a 'Semiring', with an infinite closure property:
--
-- @'star' x ≡ 'star' x '><' x '<>' 'one' ≡ x '><' 'star' x '<>' 'one'@
--
-- 'plus' can then be defined in terms of 'star':
--
-- @'plus' x ≡ ('plus' x '<>' 'one') '><' x@
--
-- If @r@ is a dioid then 'star' must be monotone:
--
-- @x '<~' y ==> 'star' x '<~' 'star' y
--
class (Monoid a, Semiring a) => Closed a where
  {-# MINIMAL star | plus #-} 
  star :: a -> a
  star a = one <> plus a

  plus :: a -> a
  plus a = a >< star a

--interior :: (r -> r) -> r -> r
--interior f r = (r ><) . f
--adjoint . star = plus . adjoint

--star = (>< zero) . (<> zero)
--plus = (<> one) . (>< one)
--star = fmap fold . some
--plus = fmap fold . many


instance Closed b => Closed (a -> b) where
  star = (.) star
  plus = (.) plus
  {-# INLINE star #-}
  {-# INLINE plus #-}

instance Closed Bool where
  star = const True -- == (|| True)
  plus = id -- == (&& True)

  {-# INLINE star #-}
  {-# INLINE plus #-}

instance Closed () where
  star  _ = ()
  plus _ = ()
  {-# INLINE star #-}
  {-# INLINE plus #-}


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
  (><) = liftA2 (<>)
  {-# INLINE (><)  #-}


instance Semigroup a => Semiring (Last a) where
  (><) = liftA2 (<>)
  {-# INLINE (><)  #-}

instance Ord a => Semiring (Max a) where
  (><) = min
  {-# INLINE (><)  #-}


instance Ord a => Semiring (Min a) where
  (><) = max
  {-# INLINE (><)  #-}


instance Semigroup a => Semiring (Either e a) where
  (><) = liftA2 (<>)
  {-# INLINE (><) #-}


-- See also 'Data.Dioid.Warning' and 'Data.Dioid.Valid'.
-- >>> (1 :| [2 :: Int]) >< (3 :| [4 :: Int])
-- 4 :| [5,5,6]
instance Semigroup a => Semiring (NonEmpty a) where
  (><) = liftA2 (<>) 
  {-# INLINE (><) #-}


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


instance Semiring Word where
  (><) = (*)
  fromBoolean = fromBooleanDef 1


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


instance (Monoid a, Monoid b, Semiring a, Semiring b) => Semiring (a, b) where
  (a, b) >< (c, d) = (a><c, b><d)
  {-# INLINE (><) #-}

  fromBoolean = liftA2 (,) fromBoolean fromBoolean


instance Monoid a => Semiring [a] where 
  (><) = liftA2 (<>)
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ pure mempty


instance (Monoid a, Semiring a) => Semiring (Maybe a) where 
  (><) = liftA2 (><)
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ pure mempty


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

  fromBoolean = fromBooleanDef $ Comparison $ \_ _ -> GT


---------------------------------------------------------------------
--  Instances (containers)
---------------------------------------------------------------------

instance Ord a => Semiring (Set.Set a) where
  (><) = Set.intersection

instance Monoid a => Semiring (Seq.Seq a) where
  (><) = liftA2 (<>)
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ Seq.singleton mempty

instance (Ord k, Monoid k, Monoid a) => Semiring (Map.Map k a) where
  xs >< ys = foldMap (flip Map.map xs . (<>)) ys
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ Map.singleton mempty mempty

instance Monoid a => Semiring (IntMap.IntMap a) where
  xs >< ys = foldMap (flip IntMap.map xs . (<>)) ys
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ IntMap.singleton 0 mempty


---------------------------------------------------------------------
-- Newtype wrappers
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

{-
--presemiring
newtype Sort a = Sort { getSort :: a }
  deriving (Eq,Ord,Show,Bounded,Generic,Generic1,Typeable,Storable,Functor)

instance Applicative Sort where
  pure = Sort
  Sort f <*> Sort a = Sort (f a)

instance Semigroup r => Semigroup (Sort r) where
  (<>) = liftA2 (<>)
  {-# INLINE (<>) #-}

instance Monoid r => Monoid (Sort r) where
  mempty = Sort mempty
  {-# INLINE mempty #-}

instance (Monoid r, Ord r) => Semiring (Sort r) where
  Sort a >< Sort b = Sort $ if a < b then a <> b else b <> a

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




-- | Provide a 'Num' instance for a 'Semiring' in which negation has no effect.
--
-- Used with GHC 8.6+'s DerivingVia extension.
--
newtype N a = N { runN :: a }
  deriving (Eq,Ord,Show,Bounded,Generic,Generic1,Typeable,Storable,Functor)

instance Semigroup r => Semigroup (N r) where
  (<>) = liftA2 (<>)
  {-# INLINE (<>) #-}

instance Monoid r => Monoid (N r) where
  mempty = N mempty
  {-# INLINE mempty #-}

instance (Monoid r, Semiring r) => Semiring (N r) where
  (><) = liftA2 (><)
  fromBoolean = N . fromBoolean

instance Applicative N where
  pure = N
  N f <*> N a = N $ f a

-- | Note that 'one' must be distinct from 'zero' for this instance to be legal.
instance (Monoid r, Semiring r) => Num (N r) where
  (+) = liftA2 (<>)
  (*) = liftA2 (><)
  negate = id
  abs = id
  signum zero = zero
  signum _ = one
  fromInteger 0 = zero
  fromInteger 1 = one
  fromInteger (-1) = one
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


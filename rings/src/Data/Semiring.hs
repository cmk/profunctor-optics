{-# Language ConstrainedClassMethods #-}

module Data.Semiring where

import Control.Applicative
import Data.Monoid hiding (First, Last)
import Data.Semigroup
import Data.Coerce (coerce)
import Numeric.Natural (Natural)

import Data.Functor.Apply
import Data.Semigroup.Foldable.Class
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
class Semigroup r => Semiring r where

  -- Multiplicative operation
  (><) :: r -> r -> r  

  -- A semiring homomorphism from the natural numbers to @r@.
  -- It needn't be injective or surjective.
  fromNatural :: Monoid r => Natural -> r
  fromNatural _ = mempty



fromNaturalDef :: Monoid r => r -> Natural -> r
fromNaturalDef _ 0 = mempty
fromNaturalDef o 1 = o
fromNaturalDef o n = fromNaturalDef o (n - 1) <> o -- TODO better implementation

foldSemiring :: (Monoid r, Semiring r) => (a -> r) -> [NonEmpty a] -> r
foldSemiring = foldMap . foldProduct

foldSemiring1 :: Semiring r => (a -> r) -> NonEmpty (NonEmpty a) -> r
foldSemiring1 = foldMap1 . foldProduct

foldProduct :: Semiring r => (a -> r) -> NonEmpty a -> r
foldProduct f (a :| []) = f a
foldProduct f (a :| b : bs) = f a >< foldProduct f (b :| bs)

--foldSum :: (Monoid r, Semiring r) => (a -> r) -> [a] -> r

-- TODO is this the same as foldSemiring when zero = one?
foldSemiring01 :: (Monoid r, Semiring r) => (a -> r) -> [[a]] -> r
foldSemiring01 f = foldMap g where g = foldr ((><) . f) one



zero :: (Monoid r, Semiring r) => r           
zero = fromNatural 0

-- | Note one may or may not equal zero.
one :: (Monoid r, Semiring r) => r
one = fromNatural 1


prop_distrib_right :: (Eq r, Semiring r) => r -> r -> r -> Bool
prop_distrib_right a b c = (a <> b) >< c == (a >< c) <> (b >< c)

prop_distrib_left :: (Eq r, Semiring r) => r -> r -> r -> Bool
prop_distrib_left a b c = a >< (b <> c) == (a >< b) <> (a >< c)

{-
https://math.stackexchange.com/questions/2777734/additive-identity-in-a-semiring-need-not-be-multiplicative-annihilator

Consider that 𝑒 is the additive identity of a hemiring 𝑆, then for any 𝑎∈𝑆, we see that 
𝑎.𝑒=𝑎.(𝑒+𝑒)= 𝑎.𝑒+𝑎.𝑒 

The step 
𝑎.𝑒+𝑎.𝑒 = 𝑎.𝑒 => 𝑎.𝑒=𝑒 will hold if the hemiring is cancellative or − 𝑎.𝑒∈𝑆. 

as a consequence of this argument, we can conclude that additive identity is not multiplicative absorber in a general hemiring (unless required axiomatically). But 𝑒 being additive identity is multiplicative absorber only if hemiring is cancellative. 

Do we prefer to use the cancellative property rather than the absorbative one?
-}

prop_zero_absorb_right :: (Eq r, Monoid r, Semiring r) => r -> Bool
prop_zero_absorb_right r = zero >< r == zero

prop_zero_neutral_right :: (Eq r, Monoid r, Semiring r) => r -> Bool
prop_zero_neutral_right r = zero <> r == r

prop_one_neutral_right :: (Eq r, Monoid r, Semiring r) => r -> Bool
prop_one_neutral_right r = one >< r == r

-- | 'fromNatural' is a Dioid homomorphism 
prop_homomorphism :: forall r. (Eq r, Monoid r, Semiring r) => Natural -> Natural -> Bool 
prop_homomorphism i j = fromNatural (i * j) == fi >< fj && fromNatural (i + j) == fi <> fj 
  where fi :: r = fromNatural i
        fj :: r = fromNatural j

--prop_one_distinct :: forall r. (Eq r, Semiring r) => Bool
--prop_one_distinct = zero /= (one :: r)


-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance Semiring Natural where
 
  (><) = (*)

  fromNatural = id


instance Semiring Bool where
 
  (><) = (&&)

  fromNatural 0 = False
  fromNatural _ = True


instance Semiring () where

  (><) _ _ = ()

  fromNatural _ = ()

--instance (Semigroup a, Semigroup b) => Semigroup (a, b)

--instance Semigroup Ordering

instance (Monoid b, Semiring b) => Semiring (a -> b) where

  (><) f g = \x -> f x >< g x

  fromNatural = const . fromNatural
  {-# INLINE (><)  #-}
  {-# INLINE fromNatural #-}


instance (Monoid a, Semiring a) => Semiring (Dual a) where
  (><) = liftA2 (><)
  fromNatural = Dual . fromNatural
  {-# INLINE (><)  #-}
  {-# INLINE fromNatural #-}


instance (Monoid a, Semiring a) => Semiring (Const a b) where
  (Const x) >< (Const y) = Const (x >< y)
  fromNatural = Const . fromNatural
  {-# INLINE (><)  #-}
  {-# INLINE fromNatural #-}

{-
-- | This instance can suffer due to floating point arithmetic.
instance Ring a => Semiring (Complex a) where
  --(x :+ y) >< (x' :+ y') = (x >< x' - (y >< y')) :+ (x >< y' + y >< x')

  (><) = liftA2 (><)
  {-# INLINE (><)  #-}

  fromNatural n = fromNatural n :+ zero
  {-# INLINE fromNatural #-}
-}

-- Note that if a happens to be an instance of Bounded then fromNatural will still work
-- but one will equal zero
instance Ord a => Semiring (Max a) where

  (><) = const

  --fromNatural = fromNaturalDef maxBound

-- TODO: pick an instance. Is this one a dioid?
instance (Bounded a, Ord a) => Semiring (Min a) where

  (><) = max

  fromNatural = fromNaturalDef minBound



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





instance Semigroup a => Semiring (NonEmpty a) where

  (><) = liftA2 (<>) 

--instance (forall a. Semigroup (f a), Semigroup a, Apply f) => Semiring (f a) where (><) = liftF2 (<>)

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


instance Monoid a => Semiring [a] where 

  (><) = liftA2 (<>)
  {-# INLINE (><) #-}

  fromNatural = fromNaturalDef $ pure mempty

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

  fromNatural = fromNaturalDef $ pure mempty

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




instance Semigroup a => Semiring (Either e a) where

  (><) = liftA2 (<>)

  -- fromNatural = fromNaturalDef $ pure mempty
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




instance Semiring Any where 

  (><) = coerce (&&)
  {-# INLINE (><) #-}

  fromNatural = fromNaturalDef $ Any True

-- Note that this instance uses 'False' as its multiplicative unit. 
instance Semiring All where 

  (><) = coerce (||)
  {-# INLINE (><) #-}

  fromNatural = fromNaturalDef $ All False


--instance (forall a. Semigroup (f a), Semigroup a, Apply f) => Semiring (f a) where (><) = liftF2 (<>)



-- Note: this instance uses the 'Alternative' monoid as the underlying semigroup.
-- Note: if 'Alternative' is ever refactored to fix the left distribution law issue then 'Alt' should be updated here as well.
instance (Monoid a, Alternative f) => Semiring (Alt f a) where

  (><) = liftA2 (<>)
  {-# INLINE (><) #-}

  fromNatural = fromNaturalDef $ pure mempty


-- Note: this instance uses the 'Applicative' monoid as the underlying semigroup.
-- Note: this instance should only be used with 'Applicative's that have no 'Alternative' instance
-- as it provides a 'Monoid' instance based on 'pure zero'.
instance (Semiring a, Applicative f) => Semiring (Ap f a) where 

  (><) = liftA2 (><)
  {-# INLINE (><) #-}

  --fromNatural = fromNaturalDef $ pure mempty

instance Semiring a => Semiring (IO a) where 

  (><) = liftA2 (><)
  {-# INLINE (><) #-}

  --fromNatural = fromNaturalDef $ pure mempty



-- | Monoid under '<.>'. Analogous to 'Data.Monoid.Product', but uses the
-- 'Semiring' constraint, rather than 'Num'.
newtype Mul a = Mul { getMul :: a }
  deriving (Eq,Ord,Show,Bounded,Generic,Generic1,Typeable,Storable,Functor)

instance Applicative Mul where
  pure = Mul
  Mul f <*> Mul a = Mul (f a)

instance Eq1 Mul where
  liftEq = coerce
  {-# INLINE liftEq #-}

instance Ord1 Mul where
  liftCompare = coerce
  {-# INLINE liftCompare #-}

{-
instance Show1 Mul where
  liftShowsPrec = showsNewtype "Mul" "getMul"
  {-# INLINE liftShowsPrec #-}
-}

instance Semiring a => Semigroup (Mul a) where
  (<>) = liftA2 (><)
  {-# INLINE (<>) #-}

instance (Monoid a, Semiring a) => Monoid (Mul a) where
  mempty = Mul one
  {-# INLINE mempty #-}


{-

-- | The semiring of endomorphisms of a semigroup under composition.
--
-- >>> let computation = End ("Hello, " ++) >< End (++ "!")
-- >>> runEnd computation "Haskell"
-- "Hello, Haskell!"

If 'a' is a commutative semigroup, the set 'End a' of endomorphisms forms a semiring, where addition is pointwise addition and multiplication is function composition. The zero morphism and the identity are the respective neutral elements. 

If A is the additive monoid of natural numbers we obtain the semiring of natural numbers as End(A), and if A = Sn with S a semiring, we obtain (after associating each morphism to a matrix) the semiring of square n-by-n matrices with coefficients in S.

This is a very useful construct. For instance, the type @forall a. 'End' ('End' a)@ is a valid encoding of church numerals, with addition and multiplication being their semiring variants.
-}

newtype End a = End { runEnd :: a -> a } -- deriving Generic

-- Note that @a@ must be a commutative semigroup for this instance to be legal.
instance Semigroup a => Semigroup (End a) where 

  End f <> End g = End $ (<>) <$> f <*> g 


instance Monoid a => Monoid (End a) where 
  
  mempty = End (mempty <>)


instance Monoid a => Semiring (End a) where 

  End f >< End g = End $ f . g
  {-# INLINE (><) #-}

  fromNatural = fromNaturalDef $ End id

{-


abst :: (Monoid a, Semiring a) => End (a -> a) -> a -> a
abst (End f) = f (one <>)



a = End $ fmap (2*) :: End (Sum Int)
b = End $ fmap (3*) :: End (Sum Int)
c = End $ fmap (4*) :: End (Sum Int)

--(a <> b) >< c == (a >< c) <> (b >< c)

rhs = (a <> b) >< c
lhs = (a >< c) <> (b >< c)

runEnd rhs $ Sum 1 -- Sum {getSum = 20}
runEnd lhs $ Sum 1 -- Sum {getSum = 20}


a = End $ fmap (2+) :: End (Sum Int)
b = End $ fmap (3+) :: End (Sum Int)
c = End $ fmap (4+) :: End (Sum Int)

rhs = (a <> b) >< c
lhs = (a >< c) <> (b >< c)

runEnd rhs $ Sum 0 -- Sum {getSum = 13}
runEnd lhs $ Sum 0 -- Sum {getSum = 13}


a = End $ fmap (2-) :: End (Sum Int)
b = End $ fmap (3-) :: End (Sum Int)
c = End $ fmap (4-) :: End (Sum Int)

rhs = (a <> b) >< c
lhs = (a >< c) <> (b >< c)

runEnd rhs $ Sum 0 -- Sum {getSum = -3}
runEnd lhs $ Sum 0 -- Sum {getSum = -3}

-}


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

  fromNatural = fromNaturalDef $ Set.singleton mempty

instance (Ord k, Monoid k, Monoid a) => Semiring (Map.Map k a) where

  xs >< ys = Foldable.foldMap (flip Map.map xs . (<>)) ys
  {-# INLINE (><) #-}

  fromNatural = fromNaturalDef $ Map.singleton mempty mempty

-- http://hackage.haskell.org/package/nonempty-containers-0.2.0.0/docs/Data-IntMap-NonEmpty.html
instance Monoid a => Semiring (IntMap.IntMap a) where

  xs >< ys = Foldable.foldMap (flip IntMap.map xs . (<>)) ys
  {-# INLINE (><) #-}

  fromNatural = fromNaturalDef $ IntMap.singleton 0 mempty


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

  --fromNatural = fromNaturalDef $ WrappedMap (Map.singleton mempty one)


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





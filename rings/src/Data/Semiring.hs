
module Data.Semiring where

import Control.Applicative
import Data.Monoid hiding (First, Last)
import Data.Semigroup
import Data.Coerce (coerce)
import GHC.Generics
import Numeric.Natural (Natural)

import Data.Functor.Apply
import Data.Semigroup.Foldable.Class
import Data.List.NonEmpty (NonEmpty(..))

import qualified Data.Foldable as Foldable
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.IntMap.Strict as IntMap

import Control.Monad (ap)

--import Data.Functor.Apply
--import Data.Functor.Bind.Class (WrappedApplicative(..))

--http://hackage.haskell.org/package/containers-0.6.0.1/docs/Data-Tree.html#g:1
-- ^ free structure for NearSemirings w/o mult identity


-- If r is a monoid then 'zero' should equal 'zero'.
-- This class does not define a (multiplicative) unit. 
-- Note that while instances should be right distributive, they need not necessarily be left-distributive (e.g. 'End')

{-

https://math.stackexchange.com/questions/2777734/additive-identity-in-a-semiring-need-not-be-multiplicative-annihilator

Consider that 𝑒 is the additive identity of a semiring 𝑆, then for any 𝑎∈𝑆, we see that 
𝑎.𝑒=𝑎.(𝑒+𝑒)= 𝑎.𝑒+𝑎.𝑒 

The step 
𝑎.𝑒+𝑎.𝑒 = 𝑎.𝑒 => 𝑎.𝑒=𝑒 will hold if the hemiring is cancellative or − 𝑎.𝑒∈𝑆. 

as a consequence of this argument, we can conclude that additive identity is not multiplicative absorber in a general semiring (unless required axiomatically). But 𝑒 being additive identity is multiplicative absorber only if semiring is cancellative. 

Do we prefer to use the cancellative property rather than the absorbative one?


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

 * A Hemiring with an additive inverse (-) is a Rng.
 * A Hemiring with a multiplicative identity (1) is a Rig.
 * A Hemiring with both of those is a Ring.
-}

-- If f is a monoid then _ should be mempty?
class Semigroup r => Semiring r where

  -- Multiplicative operation
  (><) :: r -> r -> r  

  -- fromPostive :: Positive -> r
  -- product1 :: (a -> r) -> Foldable1 (Foldable1 a) -> r
foldSemiring :: Semiring r => (a -> r) -> NonEmpty (NonEmpty a) -> r
foldSemiring f = foldMap1 g where
  g (a :| []) = f a
  g (a :| b : bs) = f a >< g (b :| bs)



prop_distrib_right :: (Eq r, Semiring r) => r -> r -> r -> Bool
prop_distrib_right a b c = (a <> b) >< c == (a >< c) <> (b >< c)

prop_distrib_left :: (Eq r, Semiring r) => r -> r -> r -> Bool
prop_distrib_left a b c = a >< (b <> c) == (a >< b) <> (a >< c)


instance Semiring () where

  (><) _ _ = ()
 

instance Ord a => Semiring (Max a) where

  (><) = flip const


instance Ord a => Semiring (Min a) where

  (><) = flip const

{-

foo = Max 2 :: Max Int
bar = Max 3 :: Max Int
baz = Max 1 :: Max Int

foo = Min 2 :: Min Int
bar = Min 3 :: Min Int
baz = Min 1 :: Min Int

prop_distrib_right baz foo bar
prop_distrib_right baz bar foo
prop_distrib_right foo bar baz
prop_distrib_right foo baz bar
prop_distrib_right bar foo baz
prop_distrib_right bar baz foo
-}




instance Semigroup a => Semiring [a] where 

  (><) = liftA2 (<>)

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


instance Semiring a => Semiring (Maybe a) where 

  (><) = liftA2 (><)
  {-# INLINE (><) #-}


{-


foo = Just $ WrappedNum 2 :: Maybe (WrappedNum Int)
bar = Just $ WrappedNum 3 :: Maybe (WrappedNum Int)
baz = Just $ WrappedNum 4 :: Maybe (WrappedNum Int)
d = Nothing :: Maybe (WrappedNum Int)
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


-- Note that this instance uses 'False' as its multiplicative unit. 
instance Semiring All where 

  (><) = coerce (||)
  {-# INLINE (><) #-}


-- Note: this instance uses the 'Alternative' monoid as the underlying semigroup.
-- Note: if 'Alternative' is ever refactored to fix the left distribution law issue then 'Alt' should be updated here as well.
instance (Semigroup a, Alternative f) => Semiring (Alt f a) where

  (><) = liftA2 (<>)
  {-# INLINE (><) #-}


-- Note: this instance uses the 'Applicative' monoid as the underlying semigroup.
-- Note: this instance should only be used with 'Applicative's that have no 'Alternative' instance
-- as it provides a 'Monoid' instance based on 'pure zero'.
instance (Semiring a, Applicative f) => Semiring (Ap f a) where 

  (><) = liftA2 (><)
  {-# INLINE (><) #-}


instance Semiring a => Semiring (IO a) where 

  (><) = liftA2 (><)
  {-# INLINE (><) #-}


---------------------------------------------------------------------
--  Instances (contravariant)
---------------------------------------------------------------------

--deriving instance Semiring (Predicate a)

--deriving instance Semiring a => Semiring (Equivalence a)

--deriving instance Semiring a => Semiring (Op a b)



---------------------------------------------------------------------
--  Instances (containers)
---------------------------------------------------------------------


--TODO nonempty instances?
instance (Ord a, Semigroup a) => Semiring (Set.Set a) where

  xs >< ys = Foldable.foldMap (flip Set.map xs . (<>)) ys
  {-# INLINE (><) #-}


instance (Ord k, Semigroup a) => Semiring (Map.Map k a) where

  xs >< ys = Foldable.foldMap (flip Map.map xs . (<>)) ys
  {-# INLINE (><) #-}

-- http://hackage.haskell.org/package/nonempty-containers-0.2.0.0/docs/Data-IntMap-NonEmpty.html
instance Semigroup a => Semiring (IntMap.IntMap a) where

  xs >< ys = Foldable.foldMap (flip IntMap.map xs . (<>)) ys
  {-# INLINE (><) #-}


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






module Data.Hemiring where

import Control.Applicative
import Data.Monoid hiding (First, Last)
import Data.Semigroup
import Data.Semiring

import Data.Coerce (coerce)
import GHC.Generics
import Numeric.Natural (Natural)

import Data.Functor.Apply
import Data.List.NonEmpty (NonEmpty(..))

import qualified Data.Foldable as Foldable
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.IntMap.Strict as IntMap


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
class Semiring r => Hemiring r where

  fromNatural :: Natural -> r


fromNaturalDef :: Semigroup r => r -> r -> Natural -> r
fromNaturalDef z _ 0 = z
fromNaturalDef _ o 1 = o
fromNaturalDef z o n = fromNaturalDef z o (n - 1) <> o
 
zero :: Hemiring r => r           
zero = fromNatural 0

one :: Hemiring r => r
one = fromNatural 1


--instance (forall a. Semigroup (f a), Semigroup a, Apply f) => Hemiring (f a) where (><) = liftF2 (<>)

prop_zero_absorb_right :: (Eq r, Hemiring r) => r -> Bool
prop_zero_absorb_right r = zero >< r == zero

prop_zero_neutral_right :: (Eq r, Hemiring r) => r -> Bool
prop_zero_neutral_right r = zero <> r == r

prop_one_neutral_right :: (Eq r, Hemiring r) => r -> Bool
prop_one_neutral_right r = one >< r == r

{-
prop_distrib_right :: (Eq r, Hemiring r) => r -> r -> r -> Bool
prop_distrib_right a b c = (a <> b) >< c == (a >< c) <> (b >< c)

prop_distrib_left :: (Eq r, Hemiring r) => r -> r -> r -> Bool
prop_distrib_left a b c = a >< (b <> c) == (a >< b) <> (a >< c)
-}






--instance (Applicative f, Hemiring a) => Hemiring (WrappedApplicative f a) where
--  sappend (WrapApplicative f) (WrapApplicative g) = WrapApplicative (sappend <$> f <.> g)

-- Orphan instances for Natural, the canonical (non-free) semiring
instance Semigroup Natural where

  (<>) = (+)


instance Monoid Natural where

  mempty = 0


instance Semiring Natural where
 
  (><) = (*)


instance Hemiring Natural where

  fromNatural = fromNaturalDef mempty 1


instance (Bounded a, Ord a) => Hemiring (Max a) where

  fromNatural = fromNaturalDef minBound maxBound


instance (Bounded a, Ord a) => Hemiring (Min a) where

  fromNatural = fromNaturalDef maxBound minBound

{-

foo = Max 2 :: Max Int
bar = Max 3 :: Max Int
baz = Max 1 :: Max Int

foo = Min 2 :: Min Int
bar = Min 3 :: Min Int
baz = Min 1 :: Min Int

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




instance Monoid a => Hemiring [a] where 

  fromNatural = fromNaturalDef mempty $ pure mempty

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


instance Hemiring a => Hemiring (Maybe a) where 

  fromNatural = fromNaturalDef mempty $ pure one

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


instance (Monoid e, Monoid a) => Hemiring (Either e a) where

  fromNatural = fromNaturalDef (Left mempty) $ pure mempty

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




instance Hemiring Any where 

  fromNatural = fromNaturalDef mempty $ Any True



-- Note that this instance uses 'False' as its multiplicative unit. 
instance Hemiring All where 

  fromNatural = fromNaturalDef mempty $ All False


-- | Provide the correct Monoid, Hemiring, and Unital instances for an arbitrary Num. Used with GHC 8.6+'s DerivingVia extension.
newtype WrappedNum a = WrappedNum { unwrappedNum :: a } deriving (Eq, Show, Num, Ord, Functor)
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


instance Num a => Hemiring (WrappedNum a) where

  fromNatural = fromNaturalDef mempty 1

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

newtype End a = End { runEnd :: a -> a } deriving Generic

-- Note that @a@ must be a commutative semigroup for this instance to be legal.
instance Semigroup a => Semigroup (End a) where 

  End f <> End g = End $ (<>) <$> f <*> g 


instance Monoid a => Monoid (End a) where 
  
  mempty = End (mempty <>)


instance Semigroup a => Semiring (End a) where 

  End f >< End g = End $ f . g
  {-# INLINE (><) #-}


instance Monoid a => Hemiring (End a) where 

  fromNatural = fromNaturalDef mempty $ End id


{-

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

-- Note: this instance uses the 'Alternative' monoid as the underlying semigroup.
-- Note: if 'Alternative' is ever refactored to fix the left distribution law issue then 'Alt' should be updated here as well.
instance (Monoid a, Alternative f) => Hemiring (Alt f a) where

  fromNatural = fromNaturalDef mempty $ pure mempty

-- Note: this instance uses the 'Applicative' monoid as the underlying semigroup.
-- Note: this instance should only be used with 'Applicative's that have no 'Alternative' instance
-- as it provides a 'Monoid' instance based on 'pure zero'.
instance (Monoid a, Hemiring a, Applicative f) => Hemiring (Ap f a) where 

  fromNatural = fromNaturalDef mempty $ pure one


instance (Monoid a, Hemiring a) => Hemiring (IO a) where 

  fromNatural = fromNaturalDef mempty $ pure one


-- | A polynomial in /x/ can be defined as a list of its coefficients,
-- where the /i/th element is the coefficient of /x^i/. 
newtype Polynomial a = Polynomial { unPolynomial :: [a] } deriving (Eq, Show)

instance Semigroup a => Semigroup (Polynomial a) where

  (Polynomial []) <> a = a
  a <> (Polynomial []) = a
  (Polynomial (x:xs)) <> (Polynomial (y:ys)) = Polynomial $ x <> y : (unPolynomial $ Polynomial xs <> Polynomial ys)


instance Semigroup a => Monoid (Polynomial a) where
  
  mempty = Polynomial []


instance Hemiring a => Semiring (Polynomial a) where

  (Polynomial xs) >< (Polynomial ys) = Polynomial $ foldr f [] ys where f x zs = map (x ><) xs <> (zero : zs)


instance Hemiring a => Hemiring (Polynomial a) where

  fromNatural = fromNaturalDef mempty $ Polynomial [one]


---------------------------------------------------------------------
--  Instances (contravariant)
---------------------------------------------------------------------

--deriving instance Hemiring (Predicate a)

--deriving instance Hemiring a => Hemiring (Equivalence a)

--deriving instance Hemiring a => Hemiring (Op a b)



---------------------------------------------------------------------
--  Instances (containers)
---------------------------------------------------------------------


instance (Ord a, Monoid a) => Hemiring (Set.Set a) where

  fromNatural = fromNaturalDef Set.empty $ Set.singleton mempty


instance (Ord k, Monoid k, Monoid a) => Hemiring (Map.Map k a) where

  fromNatural = fromNaturalDef Map.empty $ Map.singleton mempty mempty


instance Monoid a => Hemiring (IntMap.IntMap a) where

  fromNatural = fromNaturalDef IntMap.empty $ IntMap.singleton 0 mempty


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


instance (Ord k, Monoid k, Hemiring a) => Hemiring (WrappedMap k a) where

  fromNatural = fromNaturalDef mempty $ WrappedMap (Map.singleton mempty one)


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

prop_distrib_right 

rhs = foo >< (bar <> baz) 
lhs = (foo >< bar) <> (foo >< baz)

rhs = bar >< (foo <> baz) 
lhs = (bar >< foo) <> (bar >< baz)

λ> rhs
fromList [("hi",Sum {getSum = 2}),("there",Sum {getSum = 3}),("you",Sum {getSum = 3})]
λ> lhs
fromList [("hi",Sum {getSum = 2}),("there",Sum {getSum = 3}),("you",Sum {getSum = 3})]
-}





{-
Deriving Hemiring via First
Deriving Hemiring via Sum
Deriving Hemiring via Any
Deriving Hemiring via All



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

sumOf :: (Foldable t, Hemiring m) => (a -> m) -> t a -> m
productOf :: (Foldable1 t, Hemiring m) => (a -> m) -> t a -> m

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





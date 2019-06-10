
module Data.Semiring where

import Control.Applicative
import Data.Monoid hiding (First, Last)
import Data.Semigroup
import Data.Coerce (coerce)
import GHC.Generics
import Numeric.Natural (Natural)

--import Data.Functor.Apply
--import Data.List.NonEmpty

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



-- If f is a monoid then _ should be mempty?
class Semigroup r => Semiring r where
  {-# MINIMAL (><), (zero, one | fromNatural) #-}
  zero :: r           
  zero = fromNatural 0

  -- Multiplicative operation
  (><) :: r -> r -> r  

  one :: r
  one = fromNatural 1

  fromNatural :: Natural -> r
  fromNatural 0 = zero
  fromNatural 1 = one
  fromNatural n = fromNatural (n - 1) <> one -- TODO better instance
  
--instance (forall a. Semigroup (f a), Semigroup a, Apply f) => Semiring (f a) where (><) = liftF2 (<>)

prop_zero_absorb_right :: (Eq r, Semiring r) => r -> Bool
prop_zero_absorb_right r = zero >< r == zero

prop_zero_neutral_right :: (Eq r, Semiring r) => r -> Bool
prop_zero_neutral_right r = zero <> r == r

prop_one_neutral_right :: (Eq r, Semiring r) => r -> Bool
prop_one_neutral_right r = one >< r == r

prop_distrib_right :: (Eq r, Semiring r) => r -> r -> r -> Bool
prop_distrib_right a b c = (a <> b) >< c == (a >< c) <> (b >< c)

prop_distrib_left :: (Eq r, Semiring r) => r -> r -> r -> Bool
prop_distrib_left a b c = a >< (b <> c) == (a >< b) <> (a >< c)


{-
We call idempotent dioid a dioid in which the addition ⊕ is commutative and
idempotent.
34 1 Pre-Semirings, Semirings and Dioids
A frequently encountered special case is one where addition ⊕ is not only
idempotent, but selective (i.e.: ∀a, b ∈ E: a ⊕ b = a or b).
Definition 6.4.2. (selective dioid)
We call selective dioid a dioid in which the addition ⊕ is commutative and
selective.
Idempotent dioids form a particularly rich class of dioids which contains many
sub-classes, in particular:
– Doubly-idempotent dioids and distributive lattices (see Sect. 6.5);
– Doubly selective dioids (see Sect. 6.5);
– Idempotent-cancellative dioids and selective-cancellative dioids (see Sect. 6.6);
– Idempotent-invertible dioids and selective-invertible dioids (see Sect. 6.7).
-}




{-
--illegal violates absorbtion
instance Semiring a => Semiring (NonEmpty a) where
  (><) = liftA2 (<>) -- a >< b = ap ((<>) <$> a) b
  zero = pure zero
  one = pure one
-}


--instance (Applicative f, Semiring a) => Semiring (WrappedApplicative f a) where
--  sappend (WrapApplicative f) (WrapApplicative g) = WrapApplicative (sappend <$> f <.> g)

-- Orphan instances for Natural, the canonical (non-free) semiring
instance Semigroup Natural where

  (<>) = (+)


instance Monoid Natural where

  mempty = 0


instance Semiring Natural where
 
  zero = mempty

  one = 1

  (><) = (*)


instance (Bounded a, Ord a) => Semiring (Max a) where

  zero = minBound

  one = maxBound

  (><) = flip const


instance (Bounded a, Ord a) => Semiring (Min a) where

  zero = maxBound

  one = minBound

  (><) = flip const

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




instance Monoid a => Semiring [a] where 

  zero = []

  one = pure mempty

  (><) = liftA2 (<>)

{-
foo = [WrappedNum 2] :: [WrappedNum Int]
bar = [WrappedNum 1, WrappedNum 3] :: [WrappedNum Int]
baz = [WrappedNum 2, WrappedNum 3] :: [WrappedNum Int]

prop_distrib_right baz foo bar
prop_distrib_right baz bar foo
prop_distrib_right foo bar baz
prop_distrib_right foo baz bar
prop_distrib_right bar foo baz
prop_distrib_right bar baz foo
-}



instance Semiring a => Semiring (Maybe a) where 

  zero = mempty

  one = pure one

  (><) = liftA2 (><)
  {-# INLINE (><) #-}


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


instance (Monoid e, Monoid a) => Semiring (Either e a) where

  zero = Left mempty

  one = pure mempty

  (><) = liftA2 (<>)



{-
check a b | = if isLeft a && isRight b then 



check (Right _) (Left _) = False

check (Left a) (Left b) = a == b -- need Eq for this

bool False True $ isLeft

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

  zero = mempty
  one = Any $ True

  (><) = coerce (&&)
  {-# INLINE (><) #-}




-- Note that this instance uses 'False' as its multiplicative unit. 
instance Semiring All where 

  zero = mempty
  one = All $ False

  (><) = coerce (||)
  {-# INLINE (><) #-}


-- | Provide the correct Monoid, Semiring, and Unital instances for an arbitrary Num. Used with GHC 8.6+'s DerivingVia extension.
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

  zero  = mempty
  one   = 1

  (><) = (*)
  {-# INLINE (><) #-}




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

instance Monoid a => Semiring (End a) where 

  zero = mempty

  one = End id

  End f >< End g = End $ f . g
  {-# INLINE (><) #-}





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
instance (Monoid a, Alternative f) => Semiring (Alt f a) where

  zero = mempty
  one = pure mempty

  (><) = liftA2 (<>)
  {-# INLINE (><) #-}


-- Note: this instance uses the 'Applicative' monoid as the underlying semigroup.
-- Note: this instance should only be used with 'Applicative's that have no 'Alternative' instance
-- as it provides a 'Monoid' instance based on 'pure zero'.
instance (Monoid a, Semiring a, Applicative f) => Semiring (Ap f a) where 

  zero = mempty
  one = pure one

  (><) = liftA2 (><)
  {-# INLINE (><) #-}


instance (Monoid a, Semiring a) => Semiring (IO a) where 

  zero = mempty
  one = pure one

  (><) = liftA2 (><)
  {-# INLINE (><) #-}


-- | A polynomial in /x/ can be defined as a list of its coefficients,
-- where the /i/th element is the coefficient of /x^i/. 
newtype Polynomial a = Polynomial { unPolynomial :: [a] } deriving (Eq, Show)

instance Semigroup a => Semigroup (Polynomial a) where

  (Polynomial []) <> a = a
  a <> (Polynomial []) = a
  (Polynomial (x:xs)) <> (Polynomial (y:ys)) = Polynomial $ x <> y : (unPolynomial $ Polynomial xs <> Polynomial ys)

instance Semigroup a => Monoid (Polynomial a) where
  
  mempty = Polynomial []

instance Semiring a => Semiring (Polynomial a) where

  zero = mempty

  one = Polynomial [one]

  (Polynomial xs) >< (Polynomial ys) = Polynomial $ foldr f [] ys where f x zs = map (x ><) xs <> (zero : zs)



---------------------------------------------------------------------
--  Instances (contravariant)
---------------------------------------------------------------------

--deriving instance Semiring (Predicate a)

--deriving instance Semiring a => Semiring (Equivalence a)

--deriving instance Semiring a => Semiring (Op a b)



---------------------------------------------------------------------
--  Instances (containers)
---------------------------------------------------------------------


instance (Ord a, Monoid a) => Semiring (Set.Set a) where

  zero = Set.empty

  one  = Set.singleton mempty

  xs >< ys = Foldable.foldMap (flip Set.map xs . (<>)) ys
  {-# INLINE (><) #-}


instance (Ord k, Monoid k, Monoid v) => Semiring (Map.Map k v) where

  zero = Map.empty

  one  = Map.singleton mempty mempty

  xs >< ys = Foldable.foldMap (flip Map.map xs . (<>)) ys
  {-# INLINE (><) #-}


instance Monoid a => Semiring (IntMap.IntMap a) where

  zero = IntMap.empty

  one  = IntMap.singleton 0 mempty

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


-- A wrapper for 'Map' that implements a non-destructive addition.
newtype WrappedMap k v = WrappedMap { unWrappedMap :: Map.Map k v } deriving ( Eq , Ord , Show )


instance (Ord k, Semigroup v) => Semigroup (WrappedMap k v) where

  (WrappedMap xs) <> (WrappedMap ys) = WrappedMap $ Map.unionWith (<>) xs ys


instance (Ord k, Semigroup v) => Monoid (WrappedMap k v) where

  mempty = WrappedMap Map.empty

-- This semiring has both right and left distributivity.
instance (Ord k, Monoid k, Semiring v) => Semiring (WrappedMap k v) where

  zero = mempty

  one = WrappedMap $ Map.singleton mempty one

  (WrappedMap xs) >< (WrappedMap ys) = WrappedMap $ Map.fromListWith (<>) 
     [ (k <> l, v >< u) | (k, v) <- Map.toList xs, (l, u) <- Map.toList ys ]
  {-# INLINE (><) #-}


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





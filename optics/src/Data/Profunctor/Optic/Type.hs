{-# LANGUAGE UndecidableSuperClasses, TypeOperators , GADTs, DataKinds, KindSignatures, TypeFamilies #-}

{-# LANGUAGE ExistentialQuantification #-}

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveFunctor #-}

module Data.Profunctor.Optic.Type (
    module Data.Profunctor.Optic.Type
  , module Data.Profunctor.Optic.Type.Class
  , module VL
) where

import Data.Semigroup (First, Last)
import Data.Profunctor.Optic.Type.Class 
import Data.Profunctor.Optic.Prelude

import qualified Data.Profunctor.Optic.Type.VL as VL
import           Control.Applicative
import           Control.Monad
import           Control.Monad.Fix
import           Data.Bifoldable
import           Data.Bifunctor
import           Data.Bitraversable
import           Data.Coerce
import           Data.Data
import           GHC.Generics
import           Data.Distributive
import Data.Semiring hiding (Prod(..))
import Data.Functor.Classes

type Optic p s t a b = p a b -> p s t

type Optic' p s a = Optic p s s a a

type LensLike f s t a b = (a -> f b) -> s -> f t

type LensLike' f s a = LensLike f s s a a

type Equality s t a b = forall p. Optic p s t a b 

type Equality' s a = Equality s s a a

type Iso s t a b = forall p. Profunctor p => Optic p s t a b

type Iso' s a = Iso s s a a

type Lens s t a b = forall p. Strong p => Optic p s t a b

type Lens' s a = Lens s s a a

type Prism s t a b = forall p. Choice p => Optic p s t a b

type Prism' s a = Prism s s a a

type Grate s t a b = forall p. Closed p => Optic p s t a b

type Grate' s a = Grate s s a a

type Over s t a b = forall p. Mapping p => Optic p s t a b

type Over' s a = Over s s a a

type Traversal s t a b = forall p. Traversing p => Optic p s t a b

type Traversal' s a = Traversal s s a a

-- A 'Traversal0' extracts at most one result, with no monoidal interactions.
type Traversal0 s t a b = forall p. (Strong p, Choice p) => Optic p s t a b

type Traversal0' s a = Traversal0 s s a a

-- A 'Traversal1' extracts at least one result.
type Traversal1 s t a b = forall p. Traversing1 p => Optic p s t a b

type Traversal1' s a = Traversal1 s s a a

type Fold s a = forall p. (forall x. Contravariant (p x), Traversing p) => Optic' p s a

-- A 'Fold0' extracts at most one result.
type Fold0 s a = forall p. (forall x. Contravariant (p x), Strong p, Choice p) => Optic' p s a

-- A 'Fold1' extracts at least one result.
type Fold1 s a = forall p. (forall x. Contravariant (p x), Traversing1 p) => Optic' p s a 

type PrimView s t a b = forall p. (forall x. Contravariant (p x), Profunctor p) => Optic p s t a b

type PrimView' s a = PrimView s s a a

-- A 'View' extracts exactly one result.
type View s a = forall p. (forall x. Contravariant (p x), Strong p) => Optic' p s a

type PrimReview s t a b = forall p. (Bifunctor p, Profunctor p) => Optic p s t a b

type PrimReview' t b = PrimReview t t b b

type Review t b = forall p. (Bifunctor p, Choice p) => Optic' p t b


type ATraversal f s t a b = Optic (Star f) s t a b

type ATraversal' f s a = Optic' (Star f) s a

type AFold  r s a = Optic' (Star (Sum r)) s a

type AnAlt  r s a = Optic' (Star (Alt r)) s a

type AProd r s a = Optic' (Star (Prod r)) s a

type APoly r s a = Optic' (Star (Poly r)) s a

type AFold0 r s a = Optic' (Star (Pre r)) s a

--type AFold r s a = Optic' (Forget r) s a

--type AFold0 r s a = Optic' (Forget (Maybe r)) s a

type ACofold r t b = Optic' (Costar (Const r)) t b

--type AView s a = forall r. AFold r s a
type AView s a = AFold a s a

--type AReview t b = forall r. ACofold r t b
type AReview t b = ACofold b t b

type AMatch r s t a b = Optic (Star (Either r)) s t a b


unfoldMapOf :: ACofold r t b -> (r -> b) -> r -> t
unfoldMapOf = between (coDstar Const) (coUstar getConst) 



cofolded :: (Foldable f, Monoid r) => (a -> r) -> Costar f a r
cofolded f = Costar (foldMap f)

--alternated :: forall f s a. (forall f. Alternative f) => Star f s a -> Traversal s a s a
--alternated f = between runStar $ Star . (<||> f)
--alternated (Star f) = wander (<||> f)

newtype Folded r a s = Folded { runFolded :: (s -> r) -> a -> r }

-- | 'Cayley a' is isomorphic to 'End (End a)'

-- its multiplication is lens composition.
newtype Cayley a = Cayley { runCayley :: (a -> a) -> a -> a } -- deriving Generic

instance Semigroup (Cayley a) where
  (Cayley f) <> (Cayley g) = Cayley $ \h -> f h . g h

instance Monoid (Cayley a) where
  mempty = Cayley $ const id

instance Semiring (Cayley a) where
  (Cayley f) >< (Cayley g) = Cayley $ f . g

liftCayley :: (Monoid a, Semiring a) => a -> Cayley a
liftCayley x = Cayley $ \ h y -> x >< h zero <> y

lowerCayley :: (Monoid a, Semiring a) => Cayley a -> a
lowerCayley (Cayley f) = f (one <>) zero 


{-
a = liftCayley (3 :: Int)
b = liftCayley (4 :: Int)

a' = cayley (3 :: Int) 
b' = cayley (4 :: Int)


runC c = mapOf c (one <>) zero

runC $ a' . a' + b' . b'
a' . sumC a' b'


c = foo 3 4
f = foldMapping . runCayley $ c
f' = over . runCayley $ c

runC :: (Monoid a, Semiring a) => Over' a a -> a
runC c = mapOf c (one <>) zero

foldMapOf (folded . f') id [1..5]

\h -> a' h . b' h
-}
foo :: Int -> Int -> Cayley Int
foo a b = a' >< (b' <> a') 
  where a' = liftCayley a
        b' = liftCayley b
---------------------------------------------------------------------
-- 'Sum'
---------------------------------------------------------------------


newtype Sum r a = Sum { runSum :: r }
  deriving (Eq, Ord, Show, Bounded, Generic, Generic1, Typeable, Functor)

instance Contravariant (Sum r) where 

  contramap _ (Sum r) = Sum r

instance Semigroup r => Apply (Sum r) where

  Sum r <.> Sum s = Sum $ r <> s


instance (Monoid r, Semiring r) => Applicative (Sum r) where
  pure _ = Sum one

  (<*>) = (<.>)


---------------------------------------------------------------------
-- 'Product'
---------------------------------------------------------------------

--newtype Prod r a = Prod { runProd :: r } deriving (Eq, Ord, Show)

-- | Monoid under '><'. Analogous to 'Data.Monoid.Product', but uses the
-- 'Semiring' constraint, rather than 'Num'.
newtype Prod r a = Prod { unProd :: r }
  deriving (Eq, Ord, Show, Bounded, Generic, Generic1, Typeable, Functor)


{-
instance Eq1 (Prod r) where
  liftEq = coerce
  {-# INLINE liftEq #-}

instance Ord1 (Prod r) where
  liftCompare = coerce
  {-# INLINE liftCompare #-}

instance Show1 Prod where
  liftShowsPrec = showsNewtype "Mul" "getMul"
  {-# INLINE liftShowsPrec #-}
-}

instance Contravariant (Prod r) where 

  contramap _ (Prod r) = Prod r

instance Semiring r => Apply (Prod r) where

  Prod r <.> Prod s = Prod $ r >< s


instance (Monoid r, Semiring r) => Applicative (Prod r) where
  pure _ = Prod one

  (<*>) = (<.>)

{-
instance Semigroup r => Alt (Prod r) where
  Prod r <!> Prod s = Prod $ r <> s
-}

instance (Monoid r, Semiring r) => Alternative (Prod r) where
  empty = Prod mempty

  Prod r <|> Prod s = Prod $ r <> s



---------------------------------------------------------------------
-- 'Semiring'
---------------------------------------------------------------------

newtype Poly r a = Poly { runPoly :: r } 
  deriving (Eq, Ord, Show, Bounded, Generic, Generic1, Typeable, Functor)


-- | Translate between semiring ops and Applicative / Alternative ops. 
-- >>> Semi 2 <|> Semi (3::Int)
-- Semi {getSemi = 5}

{-

instance Eq1 Poly where
  liftEq = coerce
  {-# INLINE liftEq #-}

instance Ord1 Poly where
  liftCompare = coerce
  {-# INLINE liftCompare #-}

instance Show1 Mul where
  liftShowsPrec = showsNewtype "Mul" "getMul"
  {-# INLINE liftShowsPrec #-}
-}


instance Contravariant (Poly r) where 

  contramap _ (Poly r) = Poly r

instance Semiring r => Apply (Poly r) where

  Poly r <.> Poly s = Poly $ r >< s


instance Monoid r => Applicative (Poly r) where
  pure _ = Poly mempty

  Poly r <*> Poly s = Poly $ r <> s


---------------------------------------------------------------------
-- 'Alt'
---------------------------------------------------------------------


newtype Alt f a = Alt { runAlt :: f a } deriving (Eq, Ord, Show, Data, Generic, Generic1)

--instance Functor (Alt a) where fmap f (Alt p) = Alt p

instance Functor f => Functor (Alt f) where fmap f (Alt p) = Alt $ fmap f p

--instance Contravariant (Alt a) where contramap f (Alt p) = Alt p


instance Alternative f => Semigroup (Alt f a) where
  Alt a <> Alt b = Alt (a <|> b)

instance Alternative f => Monoid (Alt f a) where 
  mempty = Alt empty

--instance Alternative (Star f a)

---------------------------------------------------------------------
-- 'Pre'
---------------------------------------------------------------------

-- | 'Pre' is 'Maybe' with a phantom type variable.
--
-- 
-- Star (Pre r) a b has Strong. Also Choice & Traversing when r is a Semigroup.
-- idea: 

newtype Pre a b = Pre { runPre :: Maybe a } deriving (Eq, Ord, Show, Data, Generic, Generic1)

instance Functor (Pre a) where fmap f (Pre p) = Pre p

instance Contravariant (Pre a) where contramap f (Pre p) = Pre p


instance Semigroup a => Apply (Pre a) where

    (Pre pbc) <.> (Pre pb) = Pre $ pbc <> pb


instance Monoid a => Applicative (Pre a) where

    pure _ = Pre mempty

    (<*>) = (<.>)

{-

instance Semigroup (Pre a b) where

  Pre Nothing <> x = x

  Pre a <> _ = Pre a


instance Monoid (Pre a b) where

  mempty = Pre Nothing


instance Alt (Pre a) where

    (<!>) = (<>)


instance Monoid a => Alternative (Pre a) where

    empty = mempty

    (<|>) = (<>)

-}

{-
instance Functor Pre where
  fmap f (Pre a) = Pre (fmap f a)

instance Applicative Pre where
  pure a = Pre (Just a)
  Pre a <*> Pre b = Pre (a <*> b)
  liftA2 f (Pre x) (Pre y) = Pre (liftA2 f x y)

  Pre Nothing  *>  _ = Pre Nothing
  _               *>  b = b

instance Monad Pre where
  Pre (Just a) >>= k = k a
  _               >>= _ = Pre Nothing
  (>>) = (*>)

instance Alternative Pre where
  empty = Pre Nothing
  Pre Nothing <|> b = b
  a <|> _ = a

instance MonadPlus Pre

instance MonadFix Pre where
  mfix f = Pre (mfix (runPre . f))

instance Foldable Pre where
  foldMap f (Pre (Just m)) = f m
  foldMap _ (Pre Nothing)  = mempty

instance Traversable Pre where
  traverse f (Pre (Just a)) = Pre . Just <$> f a
  traverse _ (Pre Nothing)  = pure (Pre Nothing)
-}

---------------------------------------------------------------------
-- 'Re'
---------------------------------------------------------------------

{-

-- | A 'Monoid' for a 'Contravariant' 'Applicative'.
newtype AFold f a = AFold { getAFold :: f a }

instance (Contravariant f, Applicative f) => Semigroup (AFold f a) where
  AFold fr <> AFold fs = AFold (fr *> fs)
  {-# INLINE (<>) #-}

instance (Contravariant f, Applicative f) => Monoid (AFold f a) where
  mempty = AFold noEffect
  {-# INLINE mempty #-}
  AFold fr `mappend` AFold fs = AFold (fr *> fs)
  {-# INLINE mappend #-}
-}

---------------------------------------------------------------------
-- 'Re'
---------------------------------------------------------------------


--The 'Re' type, and its instances witness the symmetry of 'Profunctor' 
-- and the relation between 'InPhantom' and 'OutPhantom'.

newtype Re p s t a b = Re { runRe :: p b a -> p t s }

instance Profunctor p => Profunctor (Re p s t) where
    dimap f g (Re p) = Re (p . dimap g f)

instance Cochoice p => Choice (Re p s t) where
    right' (Re p) = Re (p . unright)

instance Costrong p => Strong (Re p s t) where
    first' (Re p) = Re (p . unfirst)

instance Choice p => Cochoice (Re p s t) where
    unright (Re p) = Re (p . right')

instance Strong p => Costrong (Re p s t) where
    unfirst (Re p) = Re (p . first')


---------------------------------------------------------------------
-- 
---------------------------------------------------------------------

newtype Paired p c d a b = Paired { runPaired :: p (c,a) (d,b) }

fromTambara :: Profunctor p => Tambara p a b -> Paired p d d a b
fromTambara = Paired . dimap swap swap . runTambara

instance Profunctor p => Profunctor (Paired p c d) where
  dimap f g (Paired pab) = Paired $ dimap (fmap f) (fmap g) pab

instance Strong p => Strong (Paired p c d) where
  second' (Paired pab) = Paired . dimap shuffle shuffle . second' $ pab
   where
    shuffle (x,(y,z)) = (y,(x,z))

--instance (forall x. Contravariant (p x)) => Contravariant (Paired p c d a) where
--  contramap f (Paired pab) = Paired $ contramap f pab

-- ^ @
-- paired :: Iso s t a b -> Iso s' t' a' b' -> Iso (s, s') (t, t') (a, a') (b, b')
-- paired :: Lens s t a b -> Lens s' t' a' b' -> Lens (s, s') (t, t') (a, a') (b, b')
-- @
paired 
  :: Profunctor p 
  => Optic (Paired p s' t') s t a b 
  -> Optic (Paired p a b) s' t' a' b' 
  -> Optic p (s, s') (t, t') (a, a') (b, b')
paired lab lcd = 
  dimap swap swap . runPaired . lab . Paired . 
  dimap swap swap . runPaired . lcd . Paired

pairing :: Profunctor p => (s -> a) -> (b -> t) -> Optic p (c, s) (d, t) (c, a) (d, b)
pairing f g = between runPaired Paired (dimap f g)

---------------------------------------------------------------------
-- 
---------------------------------------------------------------------

newtype Split p c d a b = Split { runSplit :: p (Either c a) (Either d b) }

fromTambaraSum :: Profunctor p => TambaraSum p a b -> Split p d d a b
fromTambaraSum = Split . dimap swap swap . runTambaraSum

instance Profunctor p => Profunctor (Split p c d) where
  dimap f g (Split pab) = Split $ dimap (fmap f) (fmap g) pab

instance Choice p => Choice (Split p c d) where
  right' (Split pab) = Split . dimap shuffle shuffle . right' $ pab
   where
    shuffle = Right . Left ||| (Left ||| Right . Right)

--instance Bifunctor p => Bifunctor (Split p c d) where
--  bimap (Split pab) = Split $ bimap pab

-- ^ @
-- split :: Iso s t a b -> Iso s' t' a' b' -> Iso (Either s s') (Either t t') (Either a a') (Either b b')
-- split :: Prism s t a b -> Prism s' t' a' b' -> Lens (Either s s') (Either t t') (Either a a') (Either b b')
-- split :: View s t a b -> View s' t' a' b' -> Review (Either s s') (Either t t') (Either a a') (Either b b')
-- @
split 
  :: Profunctor p 
  => Optic (Split p s' t') s t a b 
  -> Optic (Split p a b) s' t' a' b' 
  -> Optic p (Either s s') (Either t t') (Either a a') (Either b b')
split lab lcd = 
  dimap swap swap . runSplit . lab . Split . 
  dimap swap swap . runSplit . lcd . Split

splitting :: Profunctor p => (s -> a) -> (b -> t) -> Optic p (Either c s) (Either d t) (Either c a) (Either d b)
splitting f g = between runSplit Split (dimap f g)

---------------------------------------------------------------------
-- 'Zipped'
---------------------------------------------------------------------


newtype Zipped a b = Zipped { runZipped :: a -> a -> b }

instance Profunctor Zipped where
    dimap f g (Zipped p) = Zipped (\x y -> g (p (f x) (f y)))

instance Closed Zipped where
    closed (Zipped p) = Zipped (\f g x -> p (f x) (g x))

instance Choice Zipped where
    right' (Zipped p) = Zipped (\x y -> p <$> x <*> y)

instance Strong Zipped where
    first' (Zipped p) = Zipped (\(x, c) (y, _) -> (p x y, c))



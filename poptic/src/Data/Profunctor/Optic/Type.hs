{-# LANGUAGE UndecidableSuperClasses, TypeOperators , GADTs, DataKinds, KindSignatures, TypeFamilies #-}

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TupleSections #-}

module Data.Profunctor.Optic.Type (
    module Data.Profunctor.Optic.Type
  , module Data.Profunctor.Optic.Type.Class
  , module VL
) where

import Data.Semigroup (First, Last)
import Data.Profunctor.Optic.Type.Class 
import Data.Profunctor.Optic.Prelude
import Data.Either.Validation (Validation)

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

type Optic p s t a b = p a b -> p s t

type Optic' p s a = Optic p s s a a

type LensLike f s t a b = (a -> f b) -> s -> f t

type LensLike' f s a = LensLike f s s a a

-- | A witness that @(a ~ s, b ~ t)@.
type Equality s t a b = forall p. Optic p s t a b 

type Equality' s a = Equality s s a a

type Iso s t a b = forall p. Profunctor p => Optic p s t a b

type Iso' s a = Iso s s a a

type Lens s t a b = forall p. Strong p => Optic p s t a b

type Lens' s a = Lens s s a a

type Prism s t a b = forall p. Choice p => Optic p s t a b

type Prism' s a = Prism s s a a

-- An 'AffineFold' extracts at most one result, with no monoidal interactions.
type AffineTraversal s t a b = forall p. (Strong p, Choice p) => Optic p s t a b

type AffineTraversal' s a = AffineTraversal s s a a

type Traversal s t a b = forall p. Traversing p => Optic p s t a b

type Traversal' s a = Traversal s s a a

type Traversal1 s t a b = forall p. Traversing1 p => Optic p s t a b

type Traversal1' s a = Traversal1 s s a a

-- An 'AffineFold' extracts at most one result.
type AffineFold s a = forall p. (OutPhantom p, Strong p, Choice p) => Optic' p s a

-- | A 'Fold' describes how to retrieve multiple values in a way that can be composed
-- with other optics.
--
-- A @'Fold' s a@ provides a structure with operations very similar to those of the 'Data.Foldable.Foldable'
-- typeclass, see 'foldMapOf' and the other 'Fold' combinators.
--
-- By convention, if there exists a 'foo' method that expects a @'Data.Foldable.Foldable' (f a)@, then there should be a
-- @fooOf@ method that takes a @'Fold' s a@ and a value of type @s@. See 'Data.Profunctor.Optic.Fold'.
--
-- A 'View' is a legal 'Fold' that just ignores the supplied 'Data.Monoid.Monoid'.
--
-- Unlike a 'Traversal' a 'Fold' is read-only. Since a 'Fold' cannot be used to write back there are no laws that apply.
--

-- Folds are closed, corepresentable profunctors.
type Fold s a = forall p. (OutPhantom p, Traversing p) => Optic' p s a

-- A 'Fold1' extracts at least one result.
type Fold1 s a = forall p. (OutPhantom p, Traversing1 p) => Optic' p s a 

type Over s t a b = forall p. Mapping p => Optic p s t a b

type Over' s a = Over s s a a

type PrimView s t a b = forall p. OutPhantom p => Optic p s t a b

type PrimView' s a = PrimView s s a a

-- A 'View' extracts exactly one result.
type View s a = forall p. (OutPhantom p, Strong p) => Optic' p s a

type PrimReview s t a b = forall p. InPhantom p => Optic p s t a b

type PrimReview' t b = PrimReview t t b b

type Review t b = forall p. (InPhantom p, Choice p) => Optic' p t b

type Env s t a b = forall p. Closed p => Optic p s t a b

type Env' s a = Env s s a a

type Folding r s a = Optic' (Star (Const r)) s a

type AFolding r s a = Optic' (Star (Pre r)) s a

type Unfolding r t b = Optic' (Costar (Const r)) t b

--type Viewing s a = forall r. Folding r s a
type Viewing s a = Folding a s a

--type Reviewing t b = forall r. Unfolding r t b
type Reviewing t b = Unfolding b t b

--type Matched r = Star (Either r)

type Matching e s t a b = Optic (Matched e) s t a b

type Validated r = Star (Validation r)

type Validating e s t a b = Optic (Validated e) s t a b

--type AFolding r = Star (Pre r)
-- Folding r s a = Optic (Star (Const r)) s a
-- Folding s a = forall r. Folding r s a
--type AffineTraversed r = 

-- Retrieve either 0 or 1 subobjects, with no monoidal interactions.
type Previewing s a = Optic' (Previewed a) s a



---------------------------------------------------------------------
-- 'Matched'
---------------------------------------------------------------------

newtype Matched r a b = Matched { runMatched :: a -> Either b r }

instance Profunctor (Matched r) where
    dimap f g (Matched p) = Matched (first g . p . f)

instance Choice (Matched r) where
    right' (Matched p) = Matched (unassoc . fmap p)

instance Strong (Matched r) where
    first' (Matched p) = Matched (\(a,c) -> first (,c) (p a))

{-
instance Costrong (Matched r) where
    unfirst (Matched f) =
       Matched (first fst . f . (, error "Costrong Matched"))
-}

--TODO give this a Traversing instance or else use matching'

---------------------------------------------------------------------
-- 'Previewed'
---------------------------------------------------------------------

-- This is for Affine
newtype Previewed r a b = Previewed { runPreviewed :: a -> Maybe r }

instance Profunctor (Previewed r) where
    dimap f _ (Previewed p) = Previewed (p . f)

instance OutPhantom (Previewed r) where
    ocoerce (Previewed p) = (Previewed p)

instance Choice (Previewed r) where
    right' (Previewed p) = Previewed (either (const Nothing) p)

instance Strong (Previewed r) where
    first' (Previewed p) = Previewed (p . fst)


---------------------------------------------------------------------
-- 'Pre'
---------------------------------------------------------------------

-- | 'Pre' is 'Maybe' with a phantom type variable.
--
-- 
-- Star (Pre r) a b has Strong. Also Choice & Traversing when r is a Semigroup.
newtype Pre a b = Pre { runPre :: Maybe a } deriving (Eq, Ord, Show, Data, Generic, Generic1)

instance Functor (Pre a) where fmap f (Pre p) = Pre p

instance Contravariant (Pre a) where contramap f (Pre p) = Pre p

instance Semigroup a => Applicative (Pre a) where
    pure _ = Pre $ mempty

    (Pre pbc) <*> (Pre pb) = Pre $ pbc <> pb

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

instance InPhantom p => OutPhantom (Re p s t) where 
    ocoerce (Re p) = Re (p . icoerce)

instance OutPhantom p => InPhantom (Re p s t) where 
    icoerce (Re p) = Re (p . ocoerce)


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

instance OutPhantom p => OutPhantom (Paired p c d) where
  ocoerce (Paired pab) = Paired $ ocoerce pab

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

instance InPhantom p => InPhantom (Split p c d) where
  icoerce (Split pab) = Split $ icoerce pab

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



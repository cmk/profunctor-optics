{-# LANGUAGE UndecidableSuperClasses, TypeOperators , GADTs, DataKinds, KindSignatures, TypeFamilies #-}

{-# LANGUAGE ExistentialQuantification #-}

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE QuantifiedConstraints #-}
-- {-# LANGUAGE IncoherentInstances #-}
-- {-# LANGUAGE OverlappingInstances #-}


module Data.Profunctor.Optic.Type (
    module Data.Profunctor.Optic.Type
  , module VL
  , module Export
) where

import Data.Semigroup (First, Last)
--import Data.Profunctor.Optic.Type.Class 
import Data.Profunctor.Optic.Prelude

import qualified Data.Profunctor.Optic.Type.VL as VL
import           Control.Applicative
import           Control.Monad
import           Control.Monad.Fix
import           Data.Bifoldable
import Data.Bifunctor as Export (Bifunctor (..))
import           Data.Bitraversable
import           Data.Coerce
import           Data.Data
import           Data.Distributive
import Data.Functor.Classes

type Optic p s t a b = p a b -> p s t

type Optic' p s a = Optic p s s a a

type IsoLike f g s t a b = Optic (Adapter f g) s t a b

type LensLike f s t a b = Optic (Star f) s t a b

type LensLike' f s a = LensLike f s s a a

type GrateLike g s t a b = Optic (Costar g) s t a b

type GrateLike' g s a = GrateLike g s s a a

type Equality s t a b = forall f g. IsoLike f g s t a b 

type Equality' s a = Equality s s a a

type Iso s t a b = forall p. Profunctor p => Optic p s t a b

type Iso' s a = Iso s s a a

type Lens s t a b = forall p. Strong p => Optic p s t a b

type Lens' s a = Lens s s a a

type Prism s t a b = forall p. Choice p => Optic p s t a b

type Prism' s a = Prism s s a a

type Grate s t a b = forall p. Closed p => Optic p s t a b

type Grate' s a = Grate s s a a

-- A 'Affine' extracts at most one result, with no monoidal interactions.
type Affine s t a b = forall p. Strong p => Choice p => Optic p s t a b

type Affine' s a = Affine s s a a

type Foo s t a b = forall p. Closed p => Strong p => Optic p s t a b

type Bar s t a b = forall p. Choice p => Closed p => Optic p s t a b

type Over s t a b = forall p. Representable p => Optic p s t a b

type Under s t a b = forall p. Corepresentable p => Optic p s t a b

--type RPhantom p = forall x. Contravariant (p x)
type RPhantom p = (Representable p, Contravariant (Rep p))

type LPhantom p = (Corepresentable p, Contravariant (Corep p))
--type LPhantom p = Bifunctor p


--type Setter s t a b = forall p. Representable p => Corepresentable p => Applicative (Rep p) => Distributive (Corep p) => Optic p s t a b
-- type Setter s t a b = forall p. Strong p => Choice p => Closed p => Optic p s t a b
type Setter s t a b = forall p. Representable p => Distributive (Rep p) => Optic p s t a b

type Setter' s a = Setter s s a a

--type Resetter s t a b = forall p. Corepresentable p => ? (Corep p) => Optic p s t a b

--type Resetter' s a = Resetter s s a a


--type Traversal s t a b = forall p. Traversing p => Optic p s t a b
type Traversal s t a b = forall p. Representable p => Applicative (Rep p) => Optic p s t a b

type Traversal' s a = Traversal s s a a

--type GridVL s t a b = forall f g. (Applicative f, Functor g) => AdapterLike f g s t a b
type Grid s t a b = forall p. Corepresentable p => Distributive (Corep p) => Optic p s t a b



-- A 'Traversal1' extracts at least one result.
--type Traversal1 s t a b = forall p. Traversing1 p => Optic p s t a b

--type Traversal1' s a = Traversal1 s s a a

--type Fold s a = forall p. (forall x. Contravariant (p x), Traversing p) => Optic' p s a
--type Fold s a = forall p. RPhantom p => Strong p => Optic' p s a
type Fold s a = forall p. Representable p => Applicative (Rep p) => Contravariant (Rep p) => Optic' p s a



-- A 'AffineFold' extracts at most one result.
--type AffineFold s a = forall p. RPhantom p => Strong p => Choice p => Optic' p s a
type AffineFold s a = forall p. RPhantom p => Strong p => Choice p => Optic' p s a

-- A 'Fold1' extracts at least one result. should be able to do this w/ a GrateLike / Grid
--type Fold1 s a = forall p. RPhantom p => Traversing1 p => Optic' p s a


--type PrimGetter s t a b = forall p . Representable p => Contravariant (Rep p) => p a b -> p s t

type PrimGetter s t a b = forall p. RPhantom p => Optic p s t a b

type PrimGetter' s a = PrimGetter s s a a

type PrimReview s t a b = forall p. LPhantom p => Optic p s t a b

type PrimReview' t b = PrimReview t t b b

-- A 'Getter' extracts exactly one result.
--type Getter s a = forall p . Strong p => Representable p => Contravariant (Rep p) => p a b -> p s t
type Getter s a = forall p. RPhantom p => Strong p => Optic' p s a

type Review t b = forall p. LPhantom p => Choice p => Optic' p t b

type FoldLike r s a = LensLike' (Const r) s a

type UnfoldLike r t b = GrateLike' (Const r) t b

--type AGetter s a = forall r. FoldLike r s a
type AGetter s a = FoldLike a s a

--type AReview t b = forall r. UnfoldLike r t b
type AReview t b = UnfoldLike b t b

type ASetter s t a b = LensLike Identity s t a b

type AResetter s t a b = GrateLike Identity s t a b

type AMatch r s t a b = LensLike (Either r) s t a b


unfoldMapOf :: UnfoldLike r t b -> (r -> b) -> r -> t
unfoldMapOf = between (coDstar Const) (coUstar getConst) 

cofolded :: (Foldable f, Monoid b) => (a -> b) -> Costar f a b
cofolded f = Costar (foldMap f)


{-
toLensLike :: AdapterLike f Identity s t a b -> LensLike f s t a b
toLensLike o h = lower' o h runIdentity Identity -- l f = l (f . runIdentity) . Identity 

--fromLensLike :: AdapterLike f Identity s t a b -> LensLike f s t a b
--fromLensLike o h = lower o h Identity runIdentity 

toLensLike' o h = lower' o h getConst Const 

toGrateLike :: AdapterLike Identity g s t a b -> GrateLike g s t a b
toGrateLike o h = colower o h runIdentity Identity

toGrateLike' o h = colower o h getConst Const


lift :: LensLike f s t a b -> AdapterLike f Identity s t a b
lift l f = l (f . Identity) . runIdentity
-}

--adapt :: AdapterLike f g s t a b -> Optic (Adapter f g) s t a b
adapt = between Adapter runAdapter

--fromGrate :: GrateLike g s t a b -> Optic (Costar g) s t a b
fromGrate = between Costar runCostar

--fromLens :: LensLike f s t a b -> Optic (Star f) s t a b
fromLens = between Star runStar


--alternated :: forall f s a. (forall f. Alternative f) => Star f s a -> Traversal s a s a
--alternated f = between runStar $ Star . (<||> f)
--alternated (Star f) = wander (<||> f)


{-
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

-}



---------------------------------------------------------------------
-- 'Alt'
---------------------------------------------------------------------


newtype Alt f a = Alt { runAlt :: f a } deriving (Eq, Ord, Show, Data)

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

newtype Pre a b = Pre { runPre :: Maybe a } deriving (Eq, Ord, Show, Data)

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
newtype FoldLike f a = FoldLike { getFoldLike :: f a }

instance (Contravariant f, Applicative f) => Semigroup (FoldLike f a) where
  FoldLike fr <> FoldLike fs = FoldLike (fr *> fs)
  {-# INLINE (<>) #-}

instance (Contravariant f, Applicative f) => Monoid (FoldLike f a) where
  mempty = FoldLike noEffect
  {-# INLINE mempty #-}
  FoldLike fr `mappend` FoldLike fs = FoldLike (fr *> fs)
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
-- split :: Getter s t a b -> Getter s' t' a' b' -> Review (Either s s') (Either t t') (Either a a') (Either b b')
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



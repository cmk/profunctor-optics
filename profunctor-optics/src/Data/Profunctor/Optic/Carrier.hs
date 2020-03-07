{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE DeriveGeneric         #-}
module Data.Profunctor.Optic.Carrier (
    -- * Carrier types
    AIso
  , AIso'
  , APrism
  , APrism'
  , ALens
  , ALens'
  , ARepn
  , ARepn'
  , AGrate
  , AGrate'
  , ACorepn
  , ACorepn'
  , ATraversal0
  , ATraversal0'
  , ATraversal
  , ATraversal'
  , ATraversal1
  , ATraversal1'
  , ACotraversal0
  , ACotraversal0'
  , ACotraversal
  , ACotraversal'
  , ACotraversal1
  , ACotraversal1'
  , AList
  , AList'
  , AList1
  , AList1'
  , AScope
  , AScope'
  , AScope1
  , AScope1'
  , AFold0
  , AFold
  , AFold1
  , ACofold
  , AView
  , AReview
    -- * Primitive operators
  , withIso
  , withPrism
  , withLens
  , withGrate
  , withAffine
  , withStar
  , withCoaffine
  , withCostar
  , withFold0
  , withFold
  , withFold1
  , withCofold
  , withView
  , withReview
    -- * Carrier profunctors
  , IsoRep(..)
  , PrismRep(..)
  , Cotraversal0Rep(..)
  , LensRep(..)
  , GrateRep(..)
  , Traversal0Rep(..)
  , Fold0Rep(..)
  , Star(..)
  , Costar(..)
  , Tagged(..)
    -- * Index
  , Index(..)
  , vals
  , info
    -- * Coindex
  , Coindex(..)
  , trivial
  , noindex
  , coindex
  , (.#.)
    -- * Conjoin
  , Conjoin(..)
) where

import Control.Category (Category)
import Control.Monad.Fix (MonadFix(..))
import Data.Profunctor.Types as Export (Star(..), Costar(..))
import Data.Bifunctor as B
import Data.Function
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Combinator
import Data.Profunctor.Rep (unfirstCorep)
import GHC.Generics (Generic)

import qualified Control.Arrow as A
import qualified Control.Category as C

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> :set -XRankNTypes
-- >>> import Data.Functor.Identity
-- >>> import Data.Map as Map
-- >>> import Data.Maybe
-- >>> import Data.Monoid
-- >>> :load Data.Profunctor.Optic

---------------------------------------------------------------------
-- Carriers
---------------------------------------------------------------------

type AIso s t a b = Optic (IsoRep a b) s t a b

type AIso' s a = AIso s s a a

type APrism s t a b = Optic (PrismRep a b) s t a b

type APrism' s a = APrism s s a a

type ALens s t a b = Optic (LensRep a b) s t a b

type ALens' s a = ALens s s a a

type ARepn f s t a b = Optic (Star f) s t a b

type ARepn' f s a = ARepn f s s a a

type AGrate s t a b = Optic (GrateRep a b) s t a b

type AGrate' s a = AGrate s s a a

type ACorepn f s t a b = Optic (Costar f) s t a b

type ACorepn' f t b = ACorepn f t t b b

type ATraversal0 s t a b = Optic (Traversal0Rep a b) s t a b

type ATraversal0' s a = ATraversal0 s s a a

type ATraversal f s t a b = Applicative f => ARepn f s t a b

type ATraversal' f s a = ATraversal f s s a a

type ATraversal1 f s t a b = Apply f => ARepn f s t a b

type ATraversal1' f s a = ATraversal1 f s s a a

type ACotraversal0 s t a b = Optic (Cotraversal0Rep a b) s t a b

type ACotraversal0' s a = ACotraversal0 s s a a

type ACotraversal f s t a b = Coapplicative f => ACorepn f s t a b

type ACotraversal' f s a = ACotraversal f s s a a

type ACotraversal1 f s t a b = Coapply f => ACorepn f s t a b

type ACotraversal1' f s a = ACotraversal1 f s s a a

type AFold0 r s a = Optic' (Fold0Rep r) s a

type AFold r s a = Monoid r => ARepn' (Const r) s a

type AFold1 r s a = Semigroup r => ARepn' (Const r) s a

type ACofold r t b = ACorepn' (Const r) t b

type AList f s t a b = Foldable f => ACorepn f s t a b

type AList' f s a = AList f s s a a

type AList1 f s t a b = Foldable1 f => ACorepn f s t a b

type AList1' f s a = AList1 f s s a a

type AScope f s t a b = Traversable f => ACorepn f s t a b

type AScope' f s a = AScope f s s a a

type AScope1 f s t a b = Traversable1 f => ACorepn f s t a b

type AScope1' f s a = AScope1 f s s a a

type AView r s a = ARepn' (Const r) s a

type AReview t b = Optic' Tagged t b

-- | Extract the two functions that characterize an 'Iso'.
--
withIso :: AIso s t a b -> ((s -> a) -> (b -> t) -> r) -> r
withIso x k = case x (IsoRep id id) of IsoRep sa bt -> k sa bt
{-# INLINE withIso #-}

-- | Extract the two functions that characterize a 'Prism'.
--
withPrism :: APrism s t a b -> ((s -> t + a) -> (b -> t) -> r) -> r
withPrism o f = case o (PrismRep Right id) of PrismRep g h -> f g h
{-# INLINE withPrism #-}

-- | Extract the two functions that characterize a 'Lens'.
--
withLens :: ALens s t a b -> ((s -> a) -> (s -> b -> t) -> r) -> r
withLens o f = case o (LensRep id (flip const)) of LensRep x y -> f x y
{-# INLINE withLens #-}

-- | Extract the function that characterizes a 'Grate'.
--
withGrate :: AGrate s t a b -> ((((s -> a) -> b) -> t) -> r) -> r
withGrate o f = case o (GrateRep $ \k -> k id) of GrateRep sabt -> f sabt
{-# INLINE withGrate #-}

-- | TODO: Document
--
withAffine :: ATraversal0 s t a b -> ((s -> t + a) -> (s -> b -> t) -> r) -> r
withAffine o k = case o (Traversal0Rep Right $ const id) of Traversal0Rep x y -> k x y
{-# INLINE withAffine #-}

-- | TODO: Document
--
withStar :: ARepn f s t a b -> (a -> f b) -> s -> f t
withStar o = runStar #. o .# Star
{-# INLINE withStar #-}

-- | TODO: Document
--
withCoaffine :: ACotraversal0 s t a b -> ((((s -> t + a) -> b) -> t) -> r) -> r
withCoaffine o k = case o (Cotraversal0Rep $ \f -> f Right) of Cotraversal0Rep g -> k g
{-# INLINE withCoaffine #-}

-- | TODO: Document
--
withCostar :: ACorepn f s t a b -> (f a -> b) -> (f s -> t)
withCostar o = runCostar #. o .# Costar
{-# INLINE withCostar #-}

-- | TODO: Document
--
withFold0 :: Optic (Fold0Rep r) s t a b -> (a -> Maybe r) -> s -> Maybe r
withFold0 o = runFold0Rep #. o .# Fold0Rep
{-# INLINE withFold0 #-}

-- | Map an optic to a monoid and combine the results.
--
-- @
-- 'Data.Foldable.foldMap' = 'withFold' 'folded_'
-- @
--
-- >>> withFold both id (["foo"], ["bar", "baz"])
-- ["foo","bar","baz"]
-- >>> :t withFold traversed
-- withFold traversed
--   :: (Monoid r, Traversable f) => (a -> r) -> f a -> r
--
withFold :: Monoid r => AFold r s a -> (a -> r) -> s -> r
withFold o = (getConst #.) #. withStar o .# (Const #.)
{-# INLINE withFold #-}

-- | Map an optic to a semigroup and combine the results.
--
withFold1 :: Semigroup r => AFold1 r s a -> (a -> r) -> s -> r
withFold1 o = (getConst #.) #. withStar o .# (Const #.)
{-# INLINE withFold1 #-}

-- | TODO: Document
--
-- >>> withCofold1 (from succ) (*2) 3
-- 7
--
-- Compare 'Data.Profunctor.Optic.View.withReview'.
--
withCofold :: ACofold r t b -> (r -> b) -> r -> t
withCofold o = (.# Const) #. withCostar o .# (.# getConst) 
{-# INLINE withCofold #-}

-- | TODO: Document
--
withView :: AView r s a -> (a -> r) -> s -> r
withView o = (getConst #.) #. withStar o .# (Const #.)
{-# INLINE withView #-}

-- | TODO: Document
--
withReview :: AReview t b -> (t -> r) -> b -> r
withReview o f = f . unTagged #. o .# Tagged
{-# INLINE withReview #-}

---------------------------------------------------------------------
-- IsoRep
---------------------------------------------------------------------

-- | The 'IsoRep' profunctor precisely characterizes an 'Iso'.
data IsoRep a b s t = IsoRep (s -> a) (b -> t)

instance Profunctor (IsoRep a b) where
  dimap f g (IsoRep sa bt) = IsoRep (sa . f) (g . bt)
  {-# INLINE dimap #-}
  lmap f (IsoRep sa bt) = IsoRep (sa . f) bt
  {-# INLINE lmap #-}
  rmap f (IsoRep sa bt) = IsoRep sa (f . bt)
  {-# INLINE rmap #-}

instance Sieve (IsoRep a b) (Index a b) where
  sieve (IsoRep sa bt) s = Index (sa s) bt

instance Cosieve (IsoRep a b) (Coindex a b) where
  cosieve (IsoRep sa bt) (Coindex sab) = bt (sab sa)

---------------------------------------------------------------------
-- PrismRep
---------------------------------------------------------------------

-- | The 'PrismRep' profunctor precisely characterizes a 'Prism'.
--
data PrismRep a b s t = PrismRep (s -> t + a) (b -> t)

instance Profunctor (PrismRep a b) where
  dimap f g (PrismRep sta bt) = PrismRep (first g . sta . f) (g . bt)
  {-# INLINE dimap #-}

  lmap f (PrismRep sta bt) = PrismRep (sta . f) bt
  {-# INLINE lmap #-}

  rmap f (PrismRep sta bt) = PrismRep (first f . sta) (f . bt)
  {-# INLINE rmap #-}

instance Choice (PrismRep a b) where
  left' (PrismRep sta bt) = PrismRep (either (first Left . sta) (Left . Right)) (Left . bt)
  {-# INLINE left' #-}

  right' (PrismRep sta bt) = PrismRep (either (Left . Left) (first Right . sta)) (Right . bt)
  {-# INLINE right' #-}

---------------------------------------------------------------------
-- LensRep
---------------------------------------------------------------------

-- | The `LensRep` profunctor precisely characterizes a 'Lens'.
--
data LensRep a b s t = LensRep (s -> a) (s -> b -> t)

instance Profunctor (LensRep a b) where
  dimap f g (LensRep sa sbt) = LensRep (sa . f) (\s -> g . sbt (f s))

instance Strong (LensRep a b) where
  first' (LensRep sa sbt) =
    LensRep (\(a, _) -> sa a) (\(s, c) b -> (sbt s b, c))

  second' (LensRep sa sbt) =
    LensRep (\(_, a) -> sa a) (\(c, s) b -> (c, sbt s b))

instance Sieve (LensRep a b) (Index a b) where
  sieve (LensRep sa sbt) s = Index (sa s) (sbt s)

instance Representable (LensRep a b) where
  type Rep (LensRep a b) = Index a b

  tabulate f = LensRep (\s -> info (f s)) (\s -> vals (f s))

---------------------------------------------------------------------
-- GrateRep
---------------------------------------------------------------------

-- | The 'GrateRep' profunctor precisely characterizes 'Grate'.
--
newtype GrateRep a b s t = GrateRep { unGrateRep :: ((s -> a) -> b) -> t }

instance Profunctor (GrateRep a b) where
  dimap f g (GrateRep z) = GrateRep $ \d -> g (z $ \k -> d (k . f))

instance Closed (GrateRep a b) where
  closed (GrateRep sabt) = GrateRep $ \xsab x -> sabt $ \sa -> xsab $ \xs -> sa (xs x)

instance Costrong (GrateRep a b) where
  unfirst = unfirstCorep

instance Cosieve (GrateRep a b) (Coindex a b) where
  cosieve (GrateRep f) (Coindex g) = f g

instance Corepresentable (GrateRep a b) where
  type Corep (GrateRep a b) = Coindex a b

  cotabulate f = GrateRep $ f . Coindex

---------------------------------------------------------------------
-- Traversal0Rep
---------------------------------------------------------------------

-- | The `Traversal0Rep` profunctor precisely characterizes an 'Traversal0'.
data Traversal0Rep a b s t = Traversal0Rep (s -> t + a) (s -> b -> t)

instance Profunctor (Traversal0Rep a b) where
  dimap f g (Traversal0Rep sta sbt) = Traversal0Rep
      (\a -> first g $ sta (f a))
      (\a v -> g (sbt (f a) v))

instance Strong (Traversal0Rep a b) where
  first' (Traversal0Rep sta sbt) = Traversal0Rep
      (\(a, c) -> first (,c) $ sta a)
      (\(a, c) v -> (sbt a v, c))

instance Choice (Traversal0Rep a b) where
  right' (Traversal0Rep sta sbt) = Traversal0Rep
      (\eca -> eassocl (second sta eca))
      (\eca v -> second (`sbt` v) eca)

instance Sieve (Traversal0Rep a b) (Index0 a b) where
  sieve (Traversal0Rep sta sbt) s = Index0 (sta s) (sbt s)

instance Representable (Traversal0Rep a b) where
  type Rep (Traversal0Rep a b) = Index0 a b

  tabulate f = Traversal0Rep (info0 . f) (values0 . f)

data Index0 a b r = Index0 (r + a) (b -> r)

values0 :: Index0 a b r -> b -> r
values0 (Index0 _ br) = br

info0 :: Index0 a b r -> r + a
info0 (Index0 a _) = a

instance Functor (Index0 a b) where
  fmap f (Index0 ra br) = Index0 (first f ra) (f . br)

instance Applicative (Index0 a b) where
  pure r = Index0 (Left r) (const r)
  liftA2 f (Index0 ra1 br1) (Index0 ra2 br2) = Index0 (eswap $ liftA2 f (eswap ra1) (eswap ra2)) (liftA2 f br1 br2)

---------------------------------------------------------------------
-- Cotraversal0Rep
---------------------------------------------------------------------

--TODO: Corepresentable, Coapplicative (Corep)

-- | The 'Cotraversal0Rep' profunctor precisely characterizes 'Cotraversal0'.
--
newtype Cotraversal0Rep a b s t = Cotraversal0Rep { unCotraversal0Rep :: ((s -> t + a) -> b) -> t }

instance Profunctor (Cotraversal0Rep a b) where
  dimap us tv (Cotraversal0Rep stabt) =
    Cotraversal0Rep $ \f -> tv (stabt $ \sta -> f (first tv . sta . us))

instance Closed (Cotraversal0Rep a b) where
  closed (Cotraversal0Rep stabt) =
    Cotraversal0Rep $ \f x -> stabt $ \sta -> f $ \xs -> first const $ sta (xs x)

instance Choice (Cotraversal0Rep a b) where
  left' (Cotraversal0Rep stabt) =
    Cotraversal0Rep $ \f -> Left $ stabt $ \sta -> f $ eassocl . fmap eswap . eassocr . first sta

---------------------------------------------------------------------
-- Fold0Rep
---------------------------------------------------------------------

newtype Fold0Rep r a b = Fold0Rep { runFold0Rep :: a -> Maybe r }

instance Functor (Fold0Rep r a) where
  fmap _ (Fold0Rep p) = Fold0Rep p

instance Contravariant (Fold0Rep r a) where
  contramap _ (Fold0Rep p) = Fold0Rep p

instance Profunctor (Fold0Rep r) where
  dimap f _ (Fold0Rep p) = Fold0Rep (p . f)

instance Choice (Fold0Rep r) where
  left' (Fold0Rep p) = Fold0Rep (either p (const Nothing))
  right' (Fold0Rep p) = Fold0Rep (either (const Nothing) p)

instance Cochoice (Fold0Rep r) where
  unleft  (Fold0Rep k) = Fold0Rep (k . Left)
  unright (Fold0Rep k) = Fold0Rep (k . Right)

instance Strong (Fold0Rep r) where
  first' (Fold0Rep p) = Fold0Rep (p . fst)
  second' (Fold0Rep p) = Fold0Rep (p . snd)

instance Sieve (Fold0Rep r) (Pre r) where
  sieve = (Pre .) . runFold0Rep

instance Representable (Fold0Rep r) where
  type Rep (Fold0Rep r) = Pre r
  tabulate = Fold0Rep . (getPre .)
  {-# INLINE tabulate #-}

-- | 'Pre' is 'Maybe' with a phantom type variable.
--
newtype Pre a b = Pre { getPre :: Maybe a } deriving (Eq, Show)

instance Functor (Pre a) where fmap _ (Pre p) = Pre p

instance Contravariant (Pre a) where contramap _ (Pre p) = Pre p


---------------------------------------------------------------------
-- Index
---------------------------------------------------------------------

-- | An indexed store that characterizes a 'Data.Profunctor.Optic.Lens.Lens'
--
-- @'Index' a b s ≡ forall f. 'Functor' f => (a -> f b) -> f s@,
--
-- See also 'Data.Profunctor.Optic.Lens.withLensVl'.
--
data Index a b s = Index a (b -> s) deriving Generic

vals :: Index a b s -> b -> s
vals (Index _ bs) = bs
{-# INLINE vals #-}

info :: Index a b s -> a
info (Index a _) = a
{-# INLINE info #-}

instance Functor (Index a b) where
  fmap f (Index a bs) = Index a (f . bs)
  {-# INLINE fmap #-}

instance Profunctor (Index a) where
  dimap f g (Index a bs) = Index a (g . bs . f)
  {-# INLINE dimap #-}

instance a ~ b => Foldable (Index a b) where
  foldMap f (Index b bs) = f . bs $ b

---------------------------------------------------------------------
-- Coindex
---------------------------------------------------------------------

-- | An indexed continuation that characterizes a 'Data.Profunctor.Optic.Grate.Grate'
--
-- @'Coindex' a b s ≡ forall f. 'Functor' f => (f a -> b) -> f s@,
--
-- See also 'Data.Profunctor.Optic.Grate.withGrateVl'.
--
-- 'Coindex' can also be used to compose indexed maps, folds, or traversals directly.
--
-- For example, using the @containers@ library:
--
-- @
--  Coindex mapWithKey :: Coindex (a -> b) (Map k a -> Map k b) k
--  Coindex foldMapWithKey :: Monoid m => Coindex (a -> m) (Map k a -> m) k
--  Coindex traverseWithKey :: Applicative t => Coindex (a -> t b) (Map k a -> t (Map k b)) k
-- @
--
newtype Coindex a b s = Coindex { runCoindex :: (s -> a) -> b } deriving Generic

instance Functor (Coindex a b) where
  fmap sl (Coindex ab) = Coindex $ \la -> ab (la . sl)

instance a ~ b => Apply (Coindex a b) where
  (Coindex slab) <.> (Coindex ab) = Coindex $ \la -> slab $ \sl -> ab (la . sl) 

instance a ~ b => Applicative (Coindex a b) where
  pure s = Coindex ($s)
  (<*>) = (<.>)

trivial :: Coindex a b a -> b
trivial (Coindex f) = f id
{-# INLINE trivial #-}

-- | Lift a regular function into a coindexed function.
--
-- For example, to traverse two layers, keeping only the first index:
--
-- @
--  Coindex 'Data.Map.mapWithKey' .#. noindex 'Data.Map.map'
--    :: Monoid k =>
--       Coindex (a -> b) (Map k (Map j a) -> Map k (Map j b)) k
-- @
--
noindex :: Monoid s => (a -> b) -> Coindex a b s
noindex f = Coindex $ \a -> f (a mempty)

coindex :: Functor f => s -> (a -> b) -> Coindex (f a) (f b) s
coindex s ab = Coindex $ \sfa -> fmap ab (sfa s)
{-# INLINE coindex #-}

infixr 9 .#.

-- | Compose two coindexes.
--
-- When /s/ is a 'Monoid', 'Coindex' can be used to compose indexed traversals, folds, etc.
--
-- For example, to keep track of only the first index seen, use @Data.Monoid.First@:
--
-- @
--  fmap (First . pure) :: Coindex a b c -> Coindex a b (First c)
-- @
--
-- or keep track of all indices using a list:
--
-- @
--  fmap (:[]) :: Coindex a b c -> Coindex a b [c]
-- @
--
(.#.) :: Semigroup s => Coindex b c s -> Coindex a b s -> Coindex a c s
Coindex f .#. Coindex g = Coindex $ \b -> f $ \s1 -> g $ \s2 -> b (s1 <> s2)

---------------------------------------------------------------------
-- Conjoin
---------------------------------------------------------------------

-- '(->)' is simultaneously both indexed and co-indexed.
newtype Conjoin j a b = Conjoin { unConjoin :: j -> a -> b }

instance Functor (Conjoin j a) where
  fmap g (Conjoin f) = Conjoin $ \j a -> g (f j a)
  {-# INLINE fmap #-}

instance Apply (Conjoin j a) where
  Conjoin f <.> Conjoin g = Conjoin $ \j a -> f j a (g j a)
  {-# INLINE (<.>) #-}

instance Applicative (Conjoin j a) where
  pure b = Conjoin $ \_ _ -> b
  {-# INLINE pure #-}
  Conjoin f <*> Conjoin g = Conjoin $ \j a -> f j a (g j a)
  {-# INLINE (<*>) #-}

instance Monad (Conjoin j a) where
  return = pure
  {-# INLINE return #-}
  Conjoin f >>= k = Conjoin $ \j a -> unConjoin (k (f j a)) j a
  {-# INLINE (>>=) #-}

instance MonadFix (Conjoin j a) where
  mfix f = Conjoin $ \ j a -> let o = unConjoin (f o) j a in o
  {-# INLINE mfix #-}

instance Profunctor (Conjoin j) where
  dimap ab cd jbc = Conjoin $ \j -> cd . unConjoin jbc j . ab
  {-# INLINE dimap #-}
  lmap ab jbc = Conjoin $ \j -> unConjoin jbc j . ab
  {-# INLINE lmap #-}
  rmap bc jab = Conjoin $ \j -> bc . unConjoin jab j
  {-# INLINE rmap #-}

instance Closed (Conjoin j) where
  closed (Conjoin jab) = Conjoin $ \j xa x -> jab j (xa x)

instance Costrong (Conjoin j) where
  unfirst (Conjoin jadbd) = Conjoin $ \j a -> let
      (b, d) = jadbd j (a, d)
    in b

instance Sieve (Conjoin j) ((->) j) where
  sieve = flip . unConjoin
  {-# INLINE sieve #-}

instance Representable (Conjoin j) where
  type Rep (Conjoin j) = (->) j
  tabulate = Conjoin . flip
  {-# INLINE tabulate #-}

instance Cosieve (Conjoin j) ((,) j) where
  cosieve = uncurry . unConjoin
  {-# INLINE cosieve #-}

instance Corepresentable (Conjoin j) where
  type Corep (Conjoin j) = (,) j
  cotabulate = Conjoin . curry
  {-# INLINE cotabulate #-}

instance Choice (Conjoin j) where
  right' = A.right
  {-# INLINE right' #-}

instance Strong (Conjoin j) where
  second' = A.second
  {-# INLINE second' #-}

instance Category (Conjoin j) where
  id = Conjoin (const id)
  {-# INLINE id #-}
  Conjoin f . Conjoin g = Conjoin $ \j -> f j . g j
  {-# INLINE (.) #-}

instance A.Arrow (Conjoin j) where
  arr f = Conjoin (\_ -> f)
  {-# INLINE arr #-}
  first f = Conjoin (A.first . unConjoin f)
  {-# INLINE first #-}
  second f = Conjoin (A.second . unConjoin f)
  {-# INLINE second #-}
  Conjoin f *** Conjoin g = Conjoin $ \j -> f j A.*** g j
  {-# INLINE (***) #-}
  Conjoin f &&& Conjoin g = Conjoin $ \j -> f j A.&&& g j
  {-# INLINE (&&&) #-}

instance A.ArrowChoice (Conjoin j) where
  left f = Conjoin (A.left . unConjoin f)
  {-# INLINE left #-}
  right f = Conjoin (A.right . unConjoin f)
  {-# INLINE right #-}
  Conjoin f +++ Conjoin g = Conjoin $ \j -> f j A.+++ g j
  {-# INLINE (+++)  #-}
  Conjoin f ||| Conjoin g = Conjoin $ \j -> f j A.||| g j
  {-# INLINE (|||) #-}

instance A.ArrowApply (Conjoin j) where
  app = Conjoin $ \i (f, b) -> unConjoin f i b
  {-# INLINE app #-}

instance A.ArrowLoop (Conjoin j) where
  loop (Conjoin f) = Conjoin $ \j b -> let (c,d) = f j (b, d) in c
  {-# INLINE loop #-}

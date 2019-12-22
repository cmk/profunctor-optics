{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Carrier (
    -- * Carrier types
    AIso
  , AIso'
  , APrism
  , APrism'
  , ALens
  , ALens'
  , AIxlens
  , AIxlens'
  , AGrate
  , AGrate'
  , ACxgrate
  , ACxgrate'
  , AAffine
  , AAffine'
  , AOption
  , AIxoption
  , AGrism
  , AGrism'
  , ARepn
  , ARepn'
  , AIxrepn
  , AIxrepn'
  , ATraversal
  , ATraversal'
  , ATraversal1
  , ATraversal1'
  , AFold
  , AIxfold
  , AFold1
  , AIxfold1
  , APrimView
  , AView
  , AIxview
  , AIxsetter
  , AIxsetter'
  , ACorepn
  , ACorepn'
  , ACxrepn'
  , ACotraversal
  , ACotraversal'
  , AList
  , AList'
  , AList1
  , AList1'
  , AScope
  , AScope'
  , AScope1
  , AScope1'
  , APrimReview
  , AReview
  , ACxview
  , ACxsetter
  , ACxsetter'
    -- * Primitive operators
  , withIso
  , withPrism
  , withLens
  , withIxlens
  , withGrate
  , withCxgrate
  , withAffine
  , withGrism
  , withOption
  , withIxoption
  , withStar
  , withCostar
  , withPrimView
  , withPrimReview
  , withIxsetter
  , withCxsetter
    -- * Carrier profunctors
  , IsoRep(..)
  , PrismRep(..)
  , LensRep(..)
  , IxlensRep(..)
  , GrateRep(..)
  , CxgrateRep(..)
  , AffineRep(..)
  , GrismRep(..)
  , OptionRep(..)
  , Star(..)
  , Costar(..)
  , Tagged(..)
) where

import Data.Profunctor.Types as Export (Star(..), Costar(..))
import Data.Bifunctor as B
import Data.Function
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Index
import Data.Profunctor.Extra as Extra
import Data.Profunctor.Rep (unfirstCorep)

import qualified Data.Bifunctor as B
-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> :set -XRankNTypes
-- >>> import Control.Exception hiding (catches)
-- >>> import Data.Functor.Identity
-- >>> import Data.List.Index as LI
-- >>> import Data.Int.Instance ()
-- >>> import Data.Map as Map
-- >>> import Data.Maybe
-- >>> import Data.Monoid
-- >>> import Data.Semiring hiding (unital,nonunital,presemiring)
-- >>> :load Data.Profunctor.Optic
-- >>> let itraversed :: Ixtraversal Int [a] [b] a b ; itraversed = itraversalVl itraverse
-- >>> let iat :: Int -> Ixaffine' Int [a] a; iat i = iaffine' (\s -> flip LI.ifind s $ \n _ -> n==i) (\s a -> LI.modifyAt i (const a) s) 

---------------------------------------------------------------------
-- Carriers
---------------------------------------------------------------------

type AIso s t a b = Optic (IsoRep a b) s t a b

type AIso' s a = AIso s s a a

type APrism s t a b = Optic (PrismRep a b) s t a b

type APrism' s a = APrism s s a a

type ALens s t a b = Optic (LensRep a b) s t a b

type ALens' s a = ALens s s a a

type AIxlens i s t a b = IndexedOptic (IxlensRep i a b) i s t a b

type AIxlens' i s a = AIxlens i s s a a

type AGrate s t a b = Optic (GrateRep a b) s t a b

type AGrate' s a = AGrate s s a a

type ACxgrate k s t a b = CoindexedOptic (CxgrateRep k a b) k s t a b

type ACxgrate' k s a = ACxgrate k s s a a

type AAffine s t a b = Optic (AffineRep a b) s t a b

type AAffine' s a = AAffine s s a a

type AOption r s a = Optic' (OptionRep r) s a

type AIxoption r i s a = IndexedOptic' (OptionRep r) i s a

type AGrism s t a b = Optic (GrismRep a b) s t a b

type AGrism' s a = AGrism s s a a

type ARepn f s t a b = Optic (Star f) s t a b

type ARepn' f s a = ARepn f s s a a

type AIxrepn f i s t a b = IndexedOptic (Star f) i s t a b

type AIxrepn' f i s a = AIxrepn f i s s a a

type ATraversal f s t a b = Applicative f => ARepn f s t a b

type ATraversal' f s a = ATraversal f s s a a

type ATraversal1 f s t a b = Apply f => ARepn f s t a b

type ATraversal1' f s a = ATraversal1 f s s a a

type AFold r s a = ARepn' (Const r) s a

type AIxfold r i s a = AIxrepn' (Const r) i s a

type AFold1 r s a = ARepn' (Const r) s a

type AIxfold1 r i s a = AIxrepn' (Const r) i s a

type APrimView r s t a b = ARepn (Const r) s t a b

type AView s a = ARepn' (Const a) s a

type AIxview i s a = AIxrepn' (Const (Maybe i , a)) i s a

type AIxsetter i s t a b = IndexedOptic (->) i s t a b

type AIxsetter' i s a = AIxsetter i s s a a

type ACorepn f s t a b = Optic (Costar f) s t a b

type ACorepn' f t b = ACorepn f t t b b

type ACxrepn f k s t a b = CoindexedOptic (Costar f) k s t a b

type ACxrepn' f k t b = ACxrepn f k t t b b

type ACotraversal f s t a b = Coapplicative f => ACorepn f s t a b

type ACotraversal' f s a = ACotraversal f s s a a

type AList f s t a b = Foldable f => ACorepn f s t a b

type AList' f s a = AList f s s a a

type AList1 f s t a b = Foldable1 f => ACorepn f s t a b

type AList1' f s a = AList1 f s s a a

type AScope f s t a b = Traversable f => ACorepn f s t a b

type AScope' f s a = AScope f s s a a

type AScope1 f s t a b = Traversable1 f => ACorepn f s t a b

type AScope1' f s a = AScope1 f s s a a

type APrimReview s t a b = Optic Tagged s t a b

type AReview t b = Optic' Tagged t b

type ACxview k t b = CoindexedOptic' Tagged k t b

type ACxsetter k s t a b = CoindexedOptic (->) k s t a b

type ACxsetter' k t b = ACxsetter k t t b b

-- | Extract the two functions that characterize an 'Iso'.
--
withIso :: AIso s t a b -> ((s -> a) -> (b -> t) -> r) -> r
withIso x k = case x (IsoRep id id) of IsoRep sa bt -> k sa bt
{-# INLINE withIso #-}

-- | Extract the two functions that characterize a 'Prism'.
--
withPrism :: APrism s t a b -> ((s -> t + a) -> (b -> t) -> r) -> r
withPrism o f = case o (PrismRep Right id) of PrismRep g h -> f g h

-- | Extract the two functions that characterize a 'Lens'.
--
withLens :: ALens s t a b -> ((s -> a) -> (s -> b -> t) -> r) -> r
withLens o f = case o (LensRep id (flip const)) of LensRep x y -> f x y

-- | Extract the two functions that characterize a 'Lens'.
--
withIxlens :: Monoid i => AIxlens i s t a b -> ((s -> (i , a)) -> (s -> b -> t) -> r) -> r
withIxlens o f = case o (IxlensRep id $ flip const) of IxlensRep x y -> f (x . (mempty,)) (\s b -> y (mempty, s) b)

-- | Extract the function that characterizes a 'Grate'.
--
withGrate :: AGrate s t a b -> ((((s -> a) -> b) -> t) -> r) -> r
withGrate o f = case o (GrateRep $ \k -> k id) of GrateRep sabt -> f sabt
{-# INLINE withGrate #-}

withCxgrate :: Monoid k => ACxgrate k s t a b -> ((((s -> a) -> k -> b) -> t) -> r) -> r
withCxgrate o sakbtr = case o (CxgrateRep $ \f -> f id) of CxgrateRep sakbt -> sakbtr $ flip sakbt mempty

-- | TODO: Document
--
withAffine :: AAffine s t a b -> ((s -> t + a) -> (s -> b -> t) -> r) -> r
withAffine o k = case o (AffineRep Right $ const id) of AffineRep x y -> k x y

-- | TODO: Document
--
withGrism :: AGrism s t a b -> ((((s -> t + a) -> b) -> t) -> r) -> r
withGrism o k = case o (GrismRep $ \f -> f Right) of GrismRep g -> k g

-- | TODO: Document
--
withOption :: Optic (OptionRep r) s t a b -> (a -> Maybe r) -> s -> Maybe r
withOption o = runOptionRep #. o .# OptionRep
{-# INLINE withOption #-}

-- | TODO: Document
--
withIxoption :: Monoid i => AIxoption r i s a -> (i -> a -> Maybe r) -> s -> Maybe r
withIxoption o f = flip curry mempty $ withOption o (uncurry f)
{-# INLINE withIxoption #-}

-- | TODO: Document
--
withStar :: ARepn f s t a b -> (a -> f b) -> s -> f t
withStar o = runStar #. o .# Star
{-# INLINE withStar #-}

-- | TODO: Document
--
withCostar :: ACorepn f s t a b -> (f a -> b) -> (f s -> t)
withCostar o = runCostar #. o .# Costar
{-# INLINE withCostar #-}

-- | TODO: Document
--
withPrimView :: APrimView r s t a b -> (a -> r) -> s -> r
withPrimView o = (getConst #.) #. withStar o .# (Const #.)
{-# INLINE withPrimView #-}

-- | TODO: Document
--
withPrimReview :: APrimReview s t a b -> (t -> r) -> b -> r
withPrimReview o f = f . unTagged #. o .# Tagged
{-# INLINE withPrimReview #-}

-- | TODO: Document
--
withIxsetter :: IndexedOptic (->) i s t a b -> (i -> a -> b) -> i -> s -> t
withIxsetter o = unConjoin #. corepn o .# Conjoin
{-# INLINE withIxsetter #-}

-- | TODO: Document
--
withCxsetter :: CoindexedOptic (->) k s t a b -> (k -> a -> b) -> k -> s -> t
withCxsetter o = unConjoin #. repn o .# Conjoin
{-# INLINE withCxsetter #-}

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
-- IxlensRep
---------------------------------------------------------------------

data IxlensRep i a b s t = IxlensRep (s -> (i , a)) (s -> b -> t)

instance Profunctor (IxlensRep i a b) where
  dimap f g (IxlensRep sia sbt) = IxlensRep (sia . f) (\s -> g . sbt (f s))

instance Strong (IxlensRep i a b) where
  first' (IxlensRep sia sbt) =
    IxlensRep (\(a, _) -> sia a) (\(s, c) b -> (sbt s b, c))

  second' (IxlensRep sia sbt) =
    IxlensRep (\(_, a) -> sia a) (\(c, s) b -> (c, sbt s b))

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
-- CxgrateRep
---------------------------------------------------------------------

newtype CxgrateRep k a b s t = CxgrateRep { unCxgrateRep :: ((s -> a) -> k -> b) -> t }

--TODO Closed, Costrong

---------------------------------------------------------------------
-- AffineRep
---------------------------------------------------------------------

-- | The `AffineRep` profunctor precisely characterizes an 'Affine'.
data AffineRep a b s t = AffineRep (s -> t + a) (s -> b -> t)

instance Profunctor (AffineRep a b) where
  dimap f g (AffineRep sta sbt) = AffineRep
      (\a -> first g $ sta (f a))
      (\a v -> g (sbt (f a) v))

instance Strong (AffineRep a b) where
  first' (AffineRep sta sbt) = AffineRep
      (\(a, c) -> first (,c) $ sta a)
      (\(a, c) v -> (sbt a v, c))

instance Choice (AffineRep a b) where
  right' (AffineRep sta sbt) = AffineRep
      (\eca -> eassocl (second sta eca))
      (\eca v -> second (`sbt` v) eca)

instance Sieve (AffineRep a b) (IndexA a b) where
  sieve (AffineRep sta sbt) s = IndexA (sta s) (sbt s)

instance Representable (AffineRep a b) where
  type Rep (AffineRep a b) = IndexA a b

  tabulate f = AffineRep (info0 . f) (values0 . f)

data IndexA a b r = IndexA (r + a) (b -> r)

values0 :: IndexA a b r -> b -> r
values0 (IndexA _ br) = br

info0 :: IndexA a b r -> r + a
info0 (IndexA a _) = a

instance Functor (IndexA a b) where
  fmap f (IndexA ra br) = IndexA (first f ra) (f . br)

instance Applicative (IndexA a b) where
  pure r = IndexA (Left r) (const r)
  liftA2 f (IndexA ra1 br1) (IndexA ra2 br2) = IndexA (eswap $ liftA2 f (eswap ra1) (eswap ra2)) (liftA2 f br1 br2)

---------------------------------------------------------------------
-- 'GrismRep'
---------------------------------------------------------------------

--TODO: Corepresentable, Coapplicative (Corep)

-- | The 'GrismRep' profunctor precisely characterizes 'Grism'.
--
newtype GrismRep a b s t = GrismRep { unGrismRep :: ((s -> t + a) -> b) -> t }

instance Profunctor (GrismRep a b) where
  dimap us tv (GrismRep stabt) =
    GrismRep $ \f -> tv (stabt $ \sta -> f (first tv . sta . us))

instance Closed (GrismRep a b) where
  closed (GrismRep stabt) =
    GrismRep $ \f x -> stabt $ \sta -> f $ \xs -> first const $ sta (xs x)

instance Choice (GrismRep a b) where
  left' (GrismRep stabt) =
    GrismRep $ \f -> Left $ stabt $ \sta -> f $ eassocl . fmap eswap . eassocr . first sta

---------------------------------------------------------------------
-- OptionRep
---------------------------------------------------------------------

newtype OptionRep r a b = OptionRep { runOptionRep :: a -> Maybe r }

--todo coerce
instance Functor (OptionRep r a) where
  fmap _ (OptionRep p) = OptionRep p

instance Contravariant (OptionRep r a) where
  contramap _ (OptionRep p) = OptionRep p

instance Profunctor (OptionRep r) where
  dimap f _ (OptionRep p) = OptionRep (p . f)

instance Choice (OptionRep r) where
  left' (OptionRep p) = OptionRep (either p (const Nothing))
  right' (OptionRep p) = OptionRep (either (const Nothing) p)

instance Cochoice (OptionRep r) where
  unleft  (OptionRep k) = OptionRep (k . Left)
  unright (OptionRep k) = OptionRep (k . Right)

instance Strong (OptionRep r) where
  first' (OptionRep p) = OptionRep (p . fst)
  second' (OptionRep p) = OptionRep (p . snd)

instance Sieve (OptionRep r) (Pre r) where
  sieve = (Pre .) . runOptionRep

instance Representable (OptionRep r) where
  type Rep (OptionRep r) = Pre r
  tabulate = OptionRep . (getPre .)
  {-# INLINE tabulate #-}

-- | 'Pre' is 'Maybe' with a phantom type variable.
--
newtype Pre a b = Pre { getPre :: Maybe a } deriving (Eq, Ord, Show)

instance Functor (Pre a) where fmap _ (Pre p) = Pre p

instance Contravariant (Pre a) where contramap _ (Pre p) = Pre p

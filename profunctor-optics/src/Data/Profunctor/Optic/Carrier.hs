{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE UndecidableInstances  #-}

-- | Left and right carriers are characterized by their representation
-- functors ('Rep' and 'Corep'). 'Iso' sits at the top where both
-- are trivial ('Identity'). 'Adjoint' sits at the bottom where they
-- form a full adjunction (@'Corep' p ⊣ 'Rep' p@). A left-indexed
-- ('Ix') optic threads an index through the left adjoint functor
-- @(,) k@, while a right-indexed ('Cx') optic threads a coindex
-- through the right adjoint functor @(->) k@.
module Data.Profunctor.Optic.Carrier (
    -- * Iso Carriers
    AIso, AIso'
    -- * Star Carriers
    -- ** Lens, Ixlens
  , ALens, ALens'
  , AIxlens, AIxlens'
    -- ** Prism, Ixprism
  , APrism, APrism'
  , AIxprism, AIxprism'
    -- ** Traversal, Ixtraversal
  , ATraversal, ATraversal'
  , AIxtraversal, AIxtraversal'
    -- ** Traversal0, Ixtraversal0
  , ATraversal0, ATraversal0'
  , AIxtraversal0, AIxtraversal0'
    -- ** Traversal1, Ixtraversal1
  , ATraversal1, ATraversal1'
  , AIxtraversal1, AIxtraversal1'
    -- ** Fold, Ixfold
  , AFold, AIxfold
    -- ** Fold0, Ixfold0
  , AFold0, AIxfold0
    -- ** Fold1, Ixfold1
  , AFold1, AIxfold1
    -- ** View, Ixview
  , AView, AIxview
    -- ** Setter, Ixsetter
  , ASetter, ASetter'
  , AIxsetter, AIxsetter'
    -- ** Setter1, Ixsetter1
  , ASetter1, ASetter1'
  , AIxsetter1, AIxsetter1'
    -- * Costar Carriers
    -- ** Colens, Cxlens
  , AColens, AColens'
  , ACxlens, ACxlens'
    -- ** Relens
  , ARelens, ARelens'
    -- ** Reprism, Rxprism
  , AReprism, AReprism'
  , ARxprism, ARxprism'
    -- ** Cotraversal, Cxtraversal
  , ACotraversal, ACotraversal'
  , ACxtraversal, ACxtraversal'
    -- ** Cotraversal0
  , ACotraversal0, ACotraversal0'
    -- ** Cotraversal1, Cxtraversal1
  , ACotraversal1, ACotraversal1'
  , ACxtraversal1, ACxtraversal1'
    -- ** Cofold, Cxfold
  , ACofold, ACxfold
    -- ** Cofold1, Cxfold1
  , ACofold1, ACxfold1
    -- ** Coview, Cxview, Review
  , ACoview, ACxview, AReview
    -- ** Cosetter, Cxsetter
  , ACosetter, ACosetter'
  , ACxsetter, ACxsetter'
    -- ** Cosetter1, Cxsetter1
  , ACosetter1, ACosetter1'
  , ACxsetter1, ACxsetter1'
    -- * Adjoint Carriers
  , AAdjoint, AAdjoint'
  , AIxadjoint, AIxadjoint'
  , ACxadjoint, ACxadjoint'
    -- * Carrier operators
    -- ** Main
  , withStar
  , withFold
  , withView
  , withIso
  , withLens
  , withIxlens
  , withPrism
  , withPrism'
  , withIxprism
  , withTraversal0
  , withTraversal0'
    -- ** Dual
  , withCostar
  , withCofold
  , withReview
  , withColens
  , withCxlens
  , withRelens
  , withReprism
  , withCotraversal0
  , withCotraversal0'
  , withCotraversalVl
  , withCxtraversalVl
    -- * Carrier profunctors
    -- ** Main
  , IsoRep(..)
  , LensRep(..)
  , IxlensRep(..)
  , PrismRep(..)
  , Traversal0Rep(..)
  , Star(..)
    -- ** Dual
  , ColensRep(..)
  , CxlensRep(..)
  , RelensRep(..)
  , ReprismRep(..)
  , Cotraversal0Rep(..)
  , CotraversalRep(..)
  , CxtraversalRep(..)
  , Costar(..)
  , Tagged(..)
    -- * Paired
  , Paired(..)
  , paired
  , fromTambara
    -- * Split
  , Split(..)
  , split
  , fromTambaraSum
    -- * Index
  , Index(..)
  , vals
  , info
    -- * Coindex
  , Coindex(..)
  , trivial
  , noindex
  , coindex
  , (<<<<)
    -- * Conjoin
  , Conjoin(..)
) where

import Control.Monad.Fix (MonadFix(..))
import Data.Profunctor.Types as Export (Star(..), Costar(..))
import Data.Bifunctor as B
import Data.Function
import Data.Monoid (Alt(..))
import Data.Profunctor.Choice
import Data.Profunctor.Strong
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Import
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
-- >>> import Prelude

---------------------------------------------------------------------
-- Iso carriers
---------------------------------------------------------------------

type AIso s t a b = Optic (IsoRep a b) s t a b

type AIso' s a = AIso s s a a

---------------------------------------------------------------------
-- Lens carriers
---------------------------------------------------------------------

type ALens s t a b = Optic (LensRep a b) s t a b

type ALens' s a = ALens s s a a

type AIxlens k s t a b = Ixoptic (IxlensRep k a b) k s t a b

type AIxlens' k s a = AIxlens k s s a a

---------------------------------------------------------------------
-- Prism carriers
---------------------------------------------------------------------

type APrism s t a b = Optic (PrismRep a b) s t a b

type APrism' s a = APrism s s a a

type AIxprism k s t a b = Ixoptic (PrismRep a b) k s t a b

type AIxprism' k s a = AIxprism k s s a a

---------------------------------------------------------------------
-- Traversal carriers
---------------------------------------------------------------------

type ATraversal f s t a b = Optic (Star f) s t a b

type ATraversal' f s a = ATraversal f s s a a

type AIxtraversal f k s t a b = Ixoptic (Star f) k s t a b

type AIxtraversal' f k s a = AIxtraversal f k s s a a

type ATraversal0 s t a b = Optic (Traversal0Rep a b) s t a b

type ATraversal0' s a = ATraversal0 s s a a

type AIxtraversal0 k s t a b = Ixoptic (Traversal0Rep a b) k s t a b

type AIxtraversal0' k s a = AIxtraversal0 k s s a a

type ATraversal1 f s t a b = Optic (Star f) s t a b

type ATraversal1' f s a = ATraversal1 f s s a a

type AIxtraversal1 f k s t a b = Ixoptic (Star f) k s t a b

type AIxtraversal1' f k s a = AIxtraversal1 f k s s a a

---------------------------------------------------------------------
-- Fold carriers
---------------------------------------------------------------------

type AFold r s a = ATraversal' (Const r) s a

type AIxfold r k s a = AIxtraversal' (Const r) k s a

type AFold0 r s a = AFold (Alt Maybe r) s a

type AIxfold0 r k s a = AIxfold (Alt Maybe r) k s a

type AFold1 r s a = ATraversal1' (Const r) s a

type AIxfold1 r k s a = AIxtraversal1' (Const r) k s a

type AColens s t a b = Optic (ColensRep a b) s t a b

type AColens' s a = AColens s s a a

type ARelens s t a b = Optic (RelensRep a b) s t a b

type ARelens' s a = ARelens s s a a

type ACxlens k s t a b = Cxoptic (CxlensRep k a b) k s t a b

type ACxlens' k s a = ACxlens k s s a a

type AReprism s t a b = Optic (ReprismRep a b) s t a b

type AReprism' s a = AReprism s s a a

type ARxprism k s t a b = Ixoptic (ReprismRep a b) k s t a b

type ARxprism' k s a = ARxprism k s s a a

type ACotraversal f s t a b = Optic (Costar f) s t a b

type ACotraversal' f s a = ACotraversal f s s a a

type ACxtraversal f k s t a b = Cxoptic (Costar f) k s t a b

type ACxtraversal' f k t b = ACxtraversal f k t t b b

type ACotraversal0 s t a b = Optic (Cotraversal0Rep a b) s t a b

type ACotraversal0' s a = ACotraversal0 s s a a

type ACotraversal1 f s t a b = Optic (Costar f) s t a b

type ACotraversal1' f s a = ACotraversal1 f s s a a

type ACxtraversal1 f k s t a b = Cxoptic (Costar f) k s t a b

type ACxtraversal1' f k t b = ACxtraversal1 f k t t b b

type ACofold r t b = ACotraversal' (Const r) t b

type ACxfold r k t b = ACxtraversal' (Const r) k t b

type ACofold1 r t b = ACotraversal1' (Const r) t b

type ACxfold1 r k t b = ACxtraversal1' (Const r) k t b

---------------------------------------------------------------------
-- Setter carriers
---------------------------------------------------------------------

type ASetter s t a b = ATraversal Identity s t a b

type ASetter' s a = ASetter s s a a

type AIxsetter k s t a b = AIxtraversal Identity k s t a b

type AIxsetter' k s a = AIxsetter k s s a a

type ASetter1 s t a b = ATraversal1 Identity s t a b

type ASetter1' s a = ASetter1 s s a a

type AIxsetter1 k s t a b = AIxtraversal1 Identity k s t a b

type AIxsetter1' k s a = AIxsetter1 k s s a a

type ACosetter s t a b = ACotraversal Identity s t a b

type ACosetter' s a = ACosetter s s a a

type ACxsetter k s t a b = ACxtraversal Identity k s t a b

type ACxsetter' k t b = ACxsetter k t t b b

type ACosetter1 s t a b = ACotraversal1 Identity s t a b

type ACosetter1' s a = ACosetter1 s s a a

type ACxsetter1 k s t a b = ACxtraversal1 Identity k s t a b

type ACxsetter1' k t b = ACxsetter1 k t t b b

---------------------------------------------------------------------
-- Adjoint carriers
---------------------------------------------------------------------

-- | Monomorphized 'Adjoint' carrier.
--
-- @AAdjoint s t a b = Optic (->) s t a b = (a -> b) -> s -> t@
--
-- The @(->)@ profunctor sits at the trivial adjunction
-- @'Identity' ⊣ 'Identity'@, making it the canonical 'Adjoining'
-- profunctor for simple types. It is simultaneously
-- 'Representable' ('Rep' = 'Identity') and 'Corepresentable'
-- ('Corep' = 'Identity'), so an 'AAdjoint' can be consumed by
-- both Star-side operators ('sets', 'traverseOf') and Costar-side
-- operators ('cosets', 'cotraverseOf').
--
-- This is the meet of the optic constraint diamond:
--
-- @
--           Iso
--          / | \\
--     Lens Prism Colens
--      |    |     |
--    Setter ... Cosetter
--       \\       /
--        Adjoint
-- @
--
-- Any 'Adjoint' is simultaneously a 'Setter' and a 'Cosetter'.
-- At the carrier level, 'ASetter' = @Optic (Star Identity)@ and
-- 'ACosetter' = @Optic (Costar Identity)@ are both isomorphic to
-- @(a -> b) -> s -> t@, but GHC treats them as distinct types.
-- 'AAdjoint' = @Optic (->)@ unifies them: @(->)@ satisfies all
-- three constraint sets.
--
type AAdjoint s t a b = Optic (->) s t a b

type AAdjoint' s a = AAdjoint s s a a

type AIxadjoint k s t a b = Ixoptic (->) k s t a b

type AIxadjoint' k s a = AIxadjoint k s s a a

type ACxadjoint k s t a b = Cxoptic (->) k s t a b

type ACxadjoint' k t b = ACxadjoint k t t b b

---------------------------------------------------------------------
-- View carriers
---------------------------------------------------------------------

type AView r s a = AFold r s a

-- | A monomorphized 'Coview'. Same carrier as 'AReview' — both use
-- 'Tagged', which satisfies 'Closed', 'Costrong', and 'CoercingL'.
-- Use 'review' to extract @b -> t@ from either.
-- See "Data.Profunctor.Optic.Dual" for why these share a carrier.
type ACoview t b = Optic' Tagged t b

-- | A monomorphized 'Review'. Same carrier as 'ACoview' ('Tagged'),
-- since 'Tagged' is both 'Closed' and 'Costrong'. The 'review'
-- operator accepts both.
type AReview t b = Optic' Tagged t b

type AIxview k s a = AIxfold (k, a) k s a

-- | A monomorphized 'Cxview'. The coindex @k@ threads via @k -> b@ on
-- the right of 'Tagged', producing @b -> (k -> t)@ through 'cxview'.
--
-- There is no @ARxview@ — the hypothetical @Rxview@ threads @(k, b)@
-- on the left, which 'Tagged' discards, collapsing to 'AReview'.
type ACxview k t b = Cxoptic' Tagged k t b

---------------------------------------------------------------------
-- Carrier operators
---------------------------------------------------------------------

-- | Extract the two functions that characterize an 'Iso'.
--
withIso :: AIso s t a b -> ((s -> a) -> (b -> t) -> r) -> r
withIso x k = case x (IsoRep id id) of IsoRep sa bt -> k sa bt
{-# INLINE withIso #-}

-- | Extract the two functions that characterize a 'Lens'.
--
withLens :: ALens s t a b -> ((s -> a) -> (s -> b -> t) -> r) -> r
withLens o f = case o (LensRep id (flip const)) of LensRep x y -> f x y
{-# INLINE withLens #-}

-- | Extract the two functions that characterize an 'Ixlens'.
--
-- @since 0.0.3
withIxlens :: Monoid k => AIxlens k s t a b -> ((s -> (k , a)) -> (s -> b -> t) -> r) -> r
withIxlens o f = case o (IxlensRep id $ flip const) of IxlensRep x y -> f (x . (mempty,)) (\s b -> y (mempty, s) b)
{-# INLINE withIxlens #-}

-- | Extract the two functions that characterize a 'Prism'.
--
withPrism :: APrism s t a b -> ((s -> t + a) -> (b -> t) -> r) -> r
withPrism o f = case o (PrismRep Right id) of PrismRep g h -> f g h
{-# INLINE withPrism #-}

-- | Extract the two functions that characterize a simple 'Prism',
-- with the matcher converted to @'Maybe'@.
--
-- @since 0.0.3
withPrism' :: APrism s s a b -> ((s -> Maybe a) -> (b -> s) -> r) -> r
withPrism' o f = withPrism o $ \sta bt -> f (either (const Nothing) Just . sta) bt
{-# INLINE withPrism' #-}

-- | Extract the two functions that characterize an 'Ixprism'.
--
-- @since 0.0.3
withIxprism :: Monoid k => AIxprism k s t a b -> ((s -> t + (k , a)) -> (b -> t) -> r) -> r
withIxprism o f = case o (PrismRep (Right . snd) id) of
  PrismRep g h -> f (\s -> fmap (mempty,) (g (mempty, s))) h
{-# INLINE withIxprism #-}

-- | Extract the two functions that characterize a 'Traversal0'.
--
withTraversal0 :: ATraversal0 s t a b -> ((s -> t + a) -> (s -> b -> t) -> r) -> r
withTraversal0 o k = case o (Traversal0Rep Right $ const id) of Traversal0Rep x y -> k x y
{-# INLINE withTraversal0 #-}

-- | Extract the two functions that characterize a simple 'Traversal0',
-- with the matcher converted to @'Maybe'@.
--
-- @since 0.0.3
withTraversal0' :: ATraversal0 s s a b -> ((s -> Maybe a) -> (s -> b -> s) -> r) -> r
withTraversal0' o k = case o (Traversal0Rep Right $ const id) of Traversal0Rep x y -> k (either (const Nothing) Just . x) y
{-# INLINE withTraversal0' #-}

-- | Extract the Star (Van Laarhoven) function from an optic.
--
-- @
-- 'withStar' :: 'ATraversal' f s t a b -> (a -> f b) -> s -> f t
-- @
--
-- This is the fundamental Star-side VL extractor. 'traverseOf',
-- 'foldMapOf', and 'views' are all specializations.
--
-- See also 'withCostar' for the dual, and "Data.Profunctor.Optic.Dual"
-- for the relationship between Star and Costar.
--
withStar :: Optic (Star f) s t a b -> (a -> f b) -> s -> f t
withStar o = runStar #. o .# Star
{-# INLINE withStar #-}

-- | Extract the fold function from an optic, via 'withStar'.
--
withFold :: Monoid r => AFold r s a -> (a -> r) -> s -> r
withFold o = (getConst #.) #. withStar o .# (Const #.)
{-# INLINE withFold #-}

-- | Extract the view function from an optic, via 'withStar'.
--
withView :: AView r s a -> (a -> r) -> s -> r
withView o = (getConst #.) #. withStar o .# (Const #.)
{-# INLINE withView #-}

---------------------------------------------------------------------
-- Dual carrier operators
---------------------------------------------------------------------

-- | Extract the Costar (Van Laarhoven) function from an optic.
--
-- @
-- 'withCostar' :: 'ACotraversal' f s t a b -> (f a -> b) -> f s -> t
-- @
--
-- This is the fundamental Costar-side VL extractor. 'cotraverseOf',
-- 'cofoldMapOf', and 'reviews' are all specializations.
--
-- See also 'withStar' for the dual, and "Data.Profunctor.Optic.Dual"
-- for the relationship between Star and Costar.
--
withCostar :: Optic (Costar f) s t a b -> (f a -> b) -> f s -> t
withCostar o = runCostar #. o .# Costar
{-# INLINE withCostar #-}

-- | Extract the cofold function from an optic, via 'withCostar'.
--
withCofold :: ACofold r t b -> (r -> b) -> r -> t
withCofold o = (.# Const) #. withCostar o .# (.# getConst)
{-# INLINE withCofold #-}

-- | Extract the review function from an optic, via 'Tagged'.
--
withReview :: AReview t b -> (t -> r) -> b -> r
withReview o f = f . unTagged #. o .# Tagged
{-# INLINE withReview #-}

-- | Extract the function that characterizes a 'Colens'.
--
withColens :: AColens s t a b -> ((((s -> a) -> b) -> t) -> r) -> r
withColens o f = case o (ColensRep $ \k -> k id) of ColensRep sabt -> f sabt
{-# INLINE withColens #-}

-- | Extract the function that characterizes a 'Cxlens'.
--
-- @since 0.0.3
withCxlens :: Monoid k => ACxlens k s t a b -> ((((s -> a) -> k -> b) -> t) -> r) -> r
withCxlens o f = case o (CxlensRep ($ id)) of CxlensRep saibt -> f $ flip saibt mempty
{-# INLINE withCxlens #-}

-- | Extract the two functions that characterize a 'Relens'.
--
withRelens :: ARelens s t a b -> ((b -> s -> a) -> (b -> t) -> r) -> r
withRelens o f = case o (RelensRep (flip const) id) of RelensRep x y -> f x y
{-# INLINE withRelens #-}

-- | Extract the two functions that characterize a 'Reprism'.
--
withReprism :: AReprism s t a b -> ((s -> a) -> (b -> a + t) -> r) -> r
withReprism o f = case o (ReprismRep id Right) of ReprismRep g h -> f g h
{-# INLINE withReprism #-}

-- | Extract the function that characterizes a 'Cotraversal0'.
--
withCotraversal0 :: ACotraversal0 s t a b -> ((((s -> t + a) -> b) -> t) -> r) -> r
withCotraversal0 o k = case o (Cotraversal0Rep $ \f -> f Right) of Cotraversal0Rep g -> k g
{-# INLINE withCotraversal0 #-}

-- | Extract the function that characterizes a simple 'Cotraversal0',
-- with the matcher converted to @'Maybe'@.
--
-- @since 0.0.3
withCotraversal0' :: ACotraversal0 s s a b -> ((((s -> Maybe a) -> b) -> s) -> r) -> r
withCotraversal0' o k = withCotraversal0 o $ \stabt ->
  k (\f -> stabt (\sta -> f (either (const Nothing) Just . sta)))
{-# INLINE withCotraversal0' #-}

-- | Extract the Van Laarhoven function that characterizes a 'Cotraversal'.
--
-- @since 0.0.3
withCotraversalVl :: Optic (CotraversalRep a b) s t a b -> ((forall f. Coapplicative f => (f a -> b) -> f s -> t) -> r) -> r
withCotraversalVl o k = case o (CotraversalRep $ \fab fa -> fab fa) of
  CotraversalRep h -> k h
{-# INLINE withCotraversalVl #-}

-- | Extract the Van Laarhoven function that characterizes a 'Cxtraversal'.
--
-- @since 0.0.3
withCxtraversalVl :: Monoid k => Cxoptic (CxtraversalRep k a b) k s t a b -> ((forall f. Coapplicative f => (f a -> k -> b) -> f s -> t) -> r) -> r
withCxtraversalVl o k = case o (CxtraversalRep $ \fakb fa -> fakb fa) of
  CxtraversalRep h -> k $ \fakb fs -> h fakb fs mempty
{-# INLINE withCxtraversalVl #-}

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

instance Cosieve (IsoRep a b) (Coindex b a) where
  cosieve (IsoRep sa bt) (Coindex sab) = bt (sab sa)

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

data IxlensRep k a b s t = IxlensRep (s -> (k , a)) (s -> b -> t)

instance Profunctor (IxlensRep k a b) where
  dimap f g (IxlensRep sia sbt) = IxlensRep (sia . f) (\s -> g . sbt (f s))

instance Strong (IxlensRep k a b) where
  first' (IxlensRep sia sbt) =
    IxlensRep (\(a, _) -> sia a) (\(s, c) b -> (sbt s b, c))

  second' (IxlensRep sia sbt) =
    IxlensRep (\(_, a) -> sia a) (\(c, s) b -> (c, sbt s b))

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
-- Dual carrier profunctors
---------------------------------------------------------------------

---------------------------------------------------------------------
-- ColensRep
---------------------------------------------------------------------

-- | The 'ColensRep' profunctor precisely characterizes 'Colens'.
--
newtype ColensRep a b s t = ColensRep { unColensRep :: ((s -> a) -> b) -> t }

instance Profunctor (ColensRep a b) where
  dimap f g (ColensRep z) = ColensRep $ \d -> g (z $ \k -> d (k . f))

instance Closed (ColensRep a b) where
  closed (ColensRep sabt) = ColensRep $ \xsab x -> sabt $ \sa -> xsab $ \xs -> sa (xs x)

instance Costrong (ColensRep a b) where
  unfirst = unfirstCorep

instance Cosieve (ColensRep a b) (Coindex b a) where
  cosieve (ColensRep f) (Coindex g) = f g

instance Corepresentable (ColensRep a b) where
  type Corep (ColensRep a b) = Coindex b a

  cotabulate f = ColensRep $ f . Coindex

---------------------------------------------------------------------
-- CxlensRep
---------------------------------------------------------------------

-- @since 0.0.3
newtype CxlensRep k a b s t = CxlensRep { unCxlensRep :: ((s -> a) -> k -> b) -> t }

instance Profunctor (CxlensRep k a b) where
  dimap f g (CxlensRep z) = CxlensRep $ \d -> g (z $ \k -> d (k . f))

instance Closed (CxlensRep k a b) where
  closed (CxlensRep sabt) = CxlensRep $ \xsab x -> sabt $ \sa -> xsab $ \xs -> sa (xs x)

---------------------------------------------------------------------
-- RelensRep
---------------------------------------------------------------------

-- | The 'RelensRep' profunctor precisely characterizes a 'Relens'.
--
data RelensRep a b s t = RelensRep (b -> s -> a) (b -> t)

instance Profunctor (RelensRep a b) where
  dimap f g (RelensRep bsa bt) = RelensRep (\b s -> bsa b (f s)) (g . bt)

instance Costrong (RelensRep a b) where
  unfirst (RelensRep bsca btc) = RelensRep bsa bt
    where bsa b s = bsca b (s, snd (btc b))
          bt b    = fst (btc b)

---------------------------------------------------------------------
-- ReprismRep
---------------------------------------------------------------------

-- | The 'ReprismRep' profunctor precisely characterizes a 'Reprism'.
--
data ReprismRep a b s t = ReprismRep (s -> a) (b -> a + t)

instance Functor (ReprismRep a b s) where
  fmap f (ReprismRep sa bat) = ReprismRep sa (B.second f . bat)
  {-# INLINE fmap #-}

instance Profunctor (ReprismRep a b) where
  lmap f (ReprismRep sa bat) = ReprismRep (sa . f) bat
  {-# INLINE lmap #-}
  rmap = fmap
  {-# INLINE rmap #-}

instance Cochoice (ReprismRep a b) where
  unleft (ReprismRep sca batc) = ReprismRep (sca . Left) (forgetr $ either (eassocl . batc) Right)
  {-# INLINE unleft #-}

---------------------------------------------------------------------
-- Cotraversal0Rep
---------------------------------------------------------------------

-- Note: Cotraversal0Rep is NOT Corepresentable. The CPS form
-- @((s -> t + a) -> b) -> t@ has @t@ appearing in both the output
-- and the callback argument @s -> t + a@. A @Corep@ functor is
-- parameterized by @s@ only, but the observation function
-- @(s -> t + a) -> b@ depends on @t@ (the output type), which
-- @Corep@ cannot capture. This is unlike @ColensRep@ (where the
-- callback is @(s -> a) -> b@ with no output-type dependency) and
-- @CotraversalRep@ (where the existential over @Coapplicative f@
-- hides the dependency).
--
-- Consequence: @cotraversal0@ and @cloneCotraversal0@ cannot be
-- built via the standard @cotabulate . f . cosieve@ pattern. They
-- need a direct profunctor decomposition using @closed . right'@.

-- | The 'Cotraversal0Rep' profunctor precisely characterizes 'Cotraversal0'.
--
-- The 'Choice' instance always wraps in @Left@. This is correct: the CPS
-- encoding can only produce @t@, never @c@, so @Left t@ is the only way
-- to embed into @t + c@. See the property tests in @Test.Carrier@ for
-- verification of the left-unit law.
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
-- CotraversalRep
---------------------------------------------------------------------

-- | The 'CotraversalRep' profunctor precisely characterizes 'Cotraversal'.
--
-- It uses a rank-2 encoding, quantifying over all 'Coapplicative' functors.
-- This is analogous to how 'Costar' @f@ serves as a carrier for a specific @f@,
-- but 'CotraversalRep' is universal — it works for any 'Cotraversal' without
-- choosing @f@ upfront.
--
-- @since 0.0.3
newtype CotraversalRep a b s t = CotraversalRep
  { runCotraversalRep :: forall f. Coapplicative f => (f a -> b) -> f s -> t }

instance Profunctor (CotraversalRep a b) where
  dimap f g (CotraversalRep h) = CotraversalRep $ \fab fs -> g (h fab (fmap f fs))
  {-# INLINE dimap #-}

instance Closed (CotraversalRep a b) where
  closed (CotraversalRep h) = CotraversalRep $ \fab fxs x -> h fab (fmap ($ x) fxs)
  {-# INLINE closed #-}

instance Choice (CotraversalRep a b) where
  left' (CotraversalRep h) = CotraversalRep $ \fab fsc ->
    case coapply fsc of
      Left fs  -> Left (h fab fs)
      Right fc -> Right (copure fc)
  {-# INLINE left' #-}

instance Costrong (CotraversalRep a b) where
  unfirst = unfirstCorep
  {-# INLINE unfirst #-}

instance Cosieve (CotraversalRep a b) (CotraversalCorep b a) where
  cosieve (CotraversalRep h) (CotraversalCorep fab fs) = h fab fs
  {-# INLINE cosieve #-}

instance Corepresentable (CotraversalRep a b) where
  type Corep (CotraversalRep a b) = CotraversalCorep b a

  cotabulate f = CotraversalRep $ \fab fs -> f (CotraversalCorep fab fs)
  {-# INLINE cotabulate #-}

-- | The 'Corep' of 'CotraversalRep'. An existential pairing of a
-- 'Coapplicative' functor @f@ with an observation @f a -> b@ and a
-- value @f s@.
--
-- @since 0.0.3
data CotraversalCorep b a s where
  CotraversalCorep :: Coapplicative f => (f a -> b) -> f s -> CotraversalCorep b a s

instance Functor (CotraversalCorep b a) where
  fmap g (CotraversalCorep fab fs) = CotraversalCorep fab (fmap g fs)
  {-# INLINE fmap #-}

instance Coapply (CotraversalCorep b a) where
  coapply (CotraversalCorep fab fsc) = case coapply fsc of
    Left fs  -> Left (CotraversalCorep fab fs)
    Right fc -> Right (CotraversalCorep fab fc)
  {-# INLINE coapply #-}

instance Coapplicative (CotraversalCorep b a) where
  copure (CotraversalCorep _ fs) = copure fs
  {-# INLINE copure #-}

---------------------------------------------------------------------
-- CxtraversalRep
---------------------------------------------------------------------

-- | The 'CxtraversalRep' profunctor precisely characterizes 'Cxtraversal'.
--
-- Coindexed variant of 'CotraversalRep'.
--
-- @since 0.0.3
newtype CxtraversalRep k a b s t = CxtraversalRep
  { runCxtraversalRep :: forall f. Coapplicative f => (f a -> k -> b) -> f s -> t }

instance Profunctor (CxtraversalRep k a b) where
  dimap f g (CxtraversalRep h) = CxtraversalRep $ \fakb fs -> g (h fakb (fmap f fs))
  {-# INLINE dimap #-}

instance Closed (CxtraversalRep k a b) where
  closed (CxtraversalRep h) = CxtraversalRep $ \fakb fxs x -> h fakb (fmap ($ x) fxs)
  {-# INLINE closed #-}

instance Choice (CxtraversalRep k a b) where
  left' (CxtraversalRep h) = CxtraversalRep $ \fakb fsc ->
    case coapply fsc of
      Left fs  -> Left (h fakb fs)
      Right fc -> Right (copure fc)
  {-# INLINE left' #-}

instance Costrong (CxtraversalRep k a b) where
  unfirst = unfirstCorep
  {-# INLINE unfirst #-}

instance Cosieve (CxtraversalRep k a b) (CxtraversalCorep k b a) where
  cosieve (CxtraversalRep h) (CxtraversalCorep fakb fs) = h fakb fs
  {-# INLINE cosieve #-}

instance Corepresentable (CxtraversalRep k a b) where
  type Corep (CxtraversalRep k a b) = CxtraversalCorep k b a

  cotabulate f = CxtraversalRep $ \fakb fs -> f (CxtraversalCorep fakb fs)
  {-# INLINE cotabulate #-}

-- | The 'Corep' of 'CxtraversalRep'. Coindexed variant of 'CotraversalCorep'.
--
-- @since 0.0.3
data CxtraversalCorep k b a s where
  CxtraversalCorep :: Coapplicative f => (f a -> k -> b) -> f s -> CxtraversalCorep k b a s

instance Functor (CxtraversalCorep k b a) where
  fmap g (CxtraversalCorep fakb fs) = CxtraversalCorep fakb (fmap g fs)
  {-# INLINE fmap #-}

instance Coapply (CxtraversalCorep k b a) where
  coapply (CxtraversalCorep fakb fsc) = case coapply fsc of
    Left fs  -> Left (CxtraversalCorep fakb fs)
    Right fc -> Right (CxtraversalCorep fakb fc)
  {-# INLINE coapply #-}

instance Coapplicative (CxtraversalCorep k b a) where
  copure (CxtraversalCorep _ fs) = copure fs
  {-# INLINE copure #-}

---------------------------------------------------------------------
-- 'Paired'
---------------------------------------------------------------------

newtype Paired p c d a b = Paired { runPaired :: p (c , a) (d , b) }

fromTambara :: Profunctor p => Tambara p a b -> Paired p d d a b
fromTambara t = Paired (dimap swap swap (runTambara t))

instance Profunctor p => Profunctor (Paired p c d) where
  dimap f g (Paired pab) = Paired $ dimap (fmap f) (fmap g) pab

instance Strong p => Strong (Paired p c d) where
  second' (Paired pab) = Paired . dimap shuffle shuffle . second' $ pab
   where
    shuffle (x,(y,z)) = (y,(x,z))

-- ^ @
-- paired :: Iso s t a b -> Iso s' t' a' b' -> Iso (s, s') (t, t') (a, a') (b, b')
-- paired :: Lens s t a b -> Lens s' t' a' b' -> Lens (s, s') (t, t') (a, a') (b, b')
-- @
--
paired
  :: Profunctor p
  => Optic (Paired p s2 t2) s1 t1 a1 b1
  -> Optic (Paired p a1 b1) s2 t2 a2 b2
  -> Optic p (s1 , s2) (t1 , t2) (a1 , a2) (b1 , b2)
paired x y =
  dimap swap swap . runPaired . x . Paired . dimap swap swap . runPaired . y . Paired

---------------------------------------------------------------------
-- 'Split'
---------------------------------------------------------------------

newtype Split p c d a b = Split { runSplit :: p (c + a) (d + b) }

fromTambaraSum :: Profunctor p => TambaraSum p a b -> Split p d d a b
fromTambaraSum t = Split (dimap eswap eswap (runTambaraSum t))

instance Profunctor p => Profunctor (Split p c d) where
  dimap f g (Split pab) = Split $ dimap (fmap f) (fmap g) pab

instance Choice p => Choice (Split p c d) where
  right' (Split pab) = Split . dimap shuffle shuffle . right' $ pab
   where
    shuffle = either (Right . Left) (either Left (Right . Right))

-- ^ @
-- split :: Iso s t a b -> Iso s' t' a' b' -> Iso (s + s') (t + t') (a + a') (b + b')
-- split :: Prism s t a b -> Prism s' t' a' b' -> Lens (s + s') (t + t') (a + a') (b + b')
-- split :: View s t a b -> View s' t' a' b' -> Coview (s + s') (t + t') (a + a') (b + b')
-- @
split
  :: Profunctor p
  => Optic (Split p s2 t2) s1 t1 a1 b1
  -> Optic (Split p a1 b1) s2 t2 a2 b2
  -> Optic p (s1 + s2) (t1 + t2) (a1 + a2) (b1 + b2)
split x y =
  dimap eswap eswap . runSplit . x . Split . dimap eswap eswap . runSplit . y . Split

---------------------------------------------------------------------
-- Index
---------------------------------------------------------------------

-- | An indexed store that characterizes a 'Data.Profunctor.Optic.Lens.Lens'.
--
-- @'Index' a b s ≡ forall f. 'Functor' f => (a -> f b) -> f s@
--
-- 'Index' is the 'Rep' (representation functor) of 'LensRep':
-- @'Sieve' ('LensRep' a b) ('Index' a b)@. It lives on the
-- Strong\/Star side of the duality.
--
-- 'Index' and 'Coindex' are dual representation functors witnessing
-- the Star\/Costar duality at the functor level:
--
--   * @'Index' a a@ is 'Coapplicative' — suitable for 'Costar' \/ 'Closed'
--   * @'Coindex' a a@ is 'Applicative' — suitable for 'Star' \/ 'Strong'
--
-- Note the parameter swap: 'LensRep' @a b@ sieves to @'Index' a b@,
-- but 'ColensRep' @a b@ cosieves to @'Coindex' b a@. This swap
-- mirrors the parameter flip performed by 'Re'.
--
-- See also 'Data.Profunctor.Optic.Lens.cloneLensVl' and
-- "Data.Profunctor.Optic.Dual" for the broader duality picture.
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

--coapp f = either (Left . const) (Right . const) $ f b

instance a ~ b => Coapply (Index a b) where
  coapply (Index b bs) = bimap f g $ bs b
    where f = (Index b) . const
          g = (Index b) . const

instance a ~ b => Coapplicative (Index a b) where
  copure (Index b bs) = bs b

---------------------------------------------------------------------
-- Coindex
---------------------------------------------------------------------

-- | An indexed continuation that characterizes a 'Data.Profunctor.Optic.Lens.Colens'.
--
-- @'Coindex' a b s ≡ forall f. 'Functor' f => (f a -> b) -> f s@
--
-- 'Coindex' is the 'Corep' (corepresentation functor) of 'ColensRep':
-- @'Cosieve' ('ColensRep' a b) ('Coindex' b a)@. It lives on the
-- Closed\/Costar side of the duality.
--
-- 'Coindex' is the Star\/Costar dual of 'Index':
--
--   * @'Index' a a@ is 'Coapplicative' — suitable for 'Costar' \/ 'Closed'
--   * @'Coindex' a a@ is 'Applicative' — suitable for 'Star' \/ 'Strong'
--
-- Note the parameter swap: 'ColensRep' @a b@ cosieves to
-- @'Coindex' b a@ (not @'Coindex' a b@). This mirrors the parameter
-- flip performed by 'Re'. See "Data.Profunctor.Optic.Dual".
--
-- 'Coindex' can also be used to compose indexed maps, foldMapOf, or traversals directly.
--
-- For example, using the @containers@ library:
--
-- @
--  Coindex mapWithKey :: Coindex (a -> b) (Map k a -> Map k b) k
--  Coindex foldMapWithKey :: Monoid m => Coindex (a -> m) (Map k a -> m) k
--  Coindex traverseWithKey :: Applicative t => Coindex (a -> t b) (Map k a -> t (Map k b)) k
-- @
--
-- See also 'Data.Profunctor.Optic.Lens.cloneColensVl'.
--
newtype Coindex a b s = Coindex { runCoindex :: (s -> b) -> a } deriving Generic

instance Functor (Coindex a b) where
  fmap sl (Coindex ab) = Coindex $ \la -> ab (la . sl)

instance a ~ b => Apply (Coindex a b) where
  (Coindex slab) <.> (Coindex ab) = Coindex $ \la -> slab $ \sl -> ab (la . sl)

-- Note: Coindex a a is NOT Coapply. Coindex a a s = (s -> a) -> a is
-- the continuation monad Cont a, and continuations cannot decompose
-- over sums: coapply :: ((x + y -> a) -> a) -> ((x -> a) -> a) + ((y -> a) -> a)
-- is impossible because the continuation might use both branches
-- (e.g. \f -> f (Left x) <> f (Right y)). The (->) r instance of
-- Coapply works by sampling at mempty, but Cont has no such anchor.

instance a ~ b => Applicative (Coindex a b) where
  pure s = Coindex ($ s)
  (<*>) = (<.>)

trivial :: Coindex a b b -> a
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
noindex :: Monoid s => (b -> a) -> Coindex a b s
noindex f = Coindex $ \a -> f (a mempty)

coindex :: Functor f => s -> (b -> a) -> Coindex (f a) (f b) s
coindex s ab = Coindex $ \sfa -> fmap ab (sfa s)
{-# INLINE coindex #-}

infixr 9 <<<<

-- | Compose two coindexes.
--
-- When /s/ is a 'Monoid', 'Coindex' can be used to compose indexed traversals, foldMapOf, etc.
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
-- @since 0.0.3
(<<<<) :: Semigroup s => Coindex c b s -> Coindex b a s -> Coindex c a s
Coindex f <<<< Coindex g = Coindex $ \b -> f $ \s1 -> g $ \s2 -> b (s1 <> s2)

---------------------------------------------------------------------
-- Conjoin
---------------------------------------------------------------------

-- | Index and coindex
--
-- '(->)' is simultaneously both indexed and co-indexed. This means
-- that indexed and coindexed optics collapse to the same shape at
-- at 'Conjoin', both give 'i -> a -> k -> b' (up to argument order).
-- The distinction is purely in how the optic threads the index,
-- not in the caller's interface.
--
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
  app = Conjoin $ \k (f, b) -> unConjoin f k b
  {-# INLINE app #-}

instance A.ArrowLoop (Conjoin j) where
  loop (Conjoin f) = Conjoin $ \j b -> let (c,d) = f j (b, d) in c
  {-# INLINE loop #-}


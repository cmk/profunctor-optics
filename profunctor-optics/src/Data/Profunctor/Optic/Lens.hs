{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Lens (
    -- * Lens & Ixlens
    Lens
  , Lens'
  , lens
  , lensVl
  , matching
  , cloneLens
    -- * Optics
  , united
  , voided
  , indexed
    -- * Primitive operators
  , withLens
  , withLensVl
    -- * Operators
  , toPastro
  , toTambara
    -- * Classes
  , Strong(..)
) where

import Data.Profunctor.Strong
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Combinator
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Types
import qualified Data.Functor.Rep as F

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> import Data.Complex
-- >>> import Data.Int
-- >>> :load Data.Profunctor.Optic

---------------------------------------------------------------------
-- 'Lens' & 'Ixlens'
---------------------------------------------------------------------

-- | Obtain a 'Lens' from a getter and setter.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input functions satisfy the following
-- properties:
--
-- * @sa (sbt s a) ≡ a@
--
-- * @sbt s (sa s) ≡ s@
--
-- * @sbt (sbt s a1) a2 ≡ sbt s a2@
--
-- See 'Data.Profunctor.Optic.Property'.
--
lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens sa sbt = dimap (id &&& sa) (uncurry sbt) . second'
{-# INLINE lens #-}

-- | Transform a Van Laarhoven lens into a profunctor lens.
--
-- Compare 'Data.Profunctor.Optic.Grate.grateVl' and 'Data.Profunctor.Optic.Traversal.traversalVl'.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @abst Identity ≡ Identity@
--
-- * @fmap (abst f) . (abst g) ≡ getCompose . abst (Compose . fmap f . g)@
--
-- More generally, a profunctor optic must be monoidal as a natural 
-- transformation:
-- 
-- * @o id ≡ id@
--
-- * @o ('Data.Profunctor.Composition.Procompose' p q) ≡ 'Data.Profunctor.Composition.Procompose' (o p) (o q)@
--
lensVl :: (forall f. Functor f => (a -> f b) -> s -> f t) -> Lens s t a b
lensVl abst = dimap ((info &&& vals) . abst (flip Index id)) (uncurry id . swap) . first'
{-# INLINE lensVl #-}

-- | Obtain a 'Lens' from its free tensor representation.
--
matching :: (s -> (c , a)) -> ((c , b) -> t) -> Lens s t a b
matching sca cbt = dimap sca cbt . second'

-- | TODO: Document
--
cloneLens :: ALens s t a b -> Lens s t a b
cloneLens o = withLens o lens 

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | Extract the higher order function that characterizes a 'Lens'.
--
-- The lens laws can be stated in terms of 'withLens':
-- 
-- Identity:
-- 
-- @
-- withLensVl o Identity ≡ Identity
-- @
-- 
-- Composition:
-- 
-- @ 
-- Compose . fmap (withLensVl o f) . withLensVl o g ≡ withLensVl o (Compose . fmap f . g)
-- @
--
-- See 'Data.Profunctor.Optic.Property'.
--
withLensVl :: Functor f => ALens s t a b -> (a -> f b) -> s -> f t
withLensVl o ab s = withLens o $ \sa sbt -> sbt s <$> ab (sa s)

---------------------------------------------------------------------
-- Optics 
---------------------------------------------------------------------

-- | There is a '()' in everything.
--
-- >>> "hello" ^. united
-- ()
-- >>> "hello" & united .~ ()
-- "hello"
--
united :: Lens' a ()
united = lens (const ()) const

-- | There is everything in a 'Void'.
--
-- >>> [] & fmapped . voided <>~ "Void" 
-- []
-- >>> Nothing & fmapped . voided ..~ abs
-- Nothing
--
voided :: Lens' Void a
voided = lens absurd const

-- | Obtain a 'Lens' from a representable functor.
--
-- >>> (0 :+ 1) ^. indexed True :: Int8
-- 1
--
indexed :: F.Representable f => Eq (F.Rep f) => F.Rep f -> Lens' (f a) a
indexed i = lensVl $ lensRep i 

lensRep :: F.Representable f => Eq (F.Rep f) => F.Rep f -> forall g. Functor g => (a -> g a) -> f a -> g (f a) 
lensRep i f s = setter s <$> f (getter s)
  where getter = flip F.index i
        setter s' b = F.tabulate $ \j -> bool (F.index s' j) b (i == j)

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Use a 'Lens' to construct a 'Pastro'.
--
toPastro :: ALens s t a b -> p a b -> Pastro p s t
toPastro o p = withLens o $ \sa sbt -> Pastro (uncurry sbt . swap) p (\s -> (sa s, s))

-- | Use a 'Lens' to construct a 'Tambara'.
--
toTambara :: Strong p => ALens s t a b -> p a b -> Tambara p s t
toTambara o p = withLens o $ \sa sbt -> Tambara (first' . lens sa sbt $ p)

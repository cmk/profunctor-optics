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
  , Ixlens
  , Ixlens'
  , lens
  , ilens
  , lensVl
  , ilensVl
  , matching
  , cloneLens
    -- * Optics
  , united
  , voided
  , indexed
    -- * Indexed optics
  , ifirst
  , isecond
    -- * Primitive operators
  , withLens
  , withLensVl
  , withIxlens
    -- * Operators
  , toPastro
  , toTambara
    -- * Classes
  , Strong(..)
) where

import Data.Profunctor.Strong
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Index
import Data.Profunctor.Optic.Types
import Data.Semiring.Module

import qualified Data.Bifunctor as B
import qualified Data.Functor.Rep as F

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> import Data.Int.Instance ()
-- >>> import Data.Semiring.V2
-- >>> import Data.Semiring.V3
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

-- | Obtain an indexed 'Lens' from an indexed getter and a setter.
--
-- Compare 'lens' and 'Data.Profunctor.Optic.Traversal.itraversal'.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input functions constitute a legal 
-- indexed lens:
--
-- * @snd . sia (sbt s a) ≡ a@
--
-- * @sbt s (snd $ sia s) ≡ s@
--
-- * @sbt (sbt s a1) a2 ≡ sbt s a2@
--
-- See 'Data.Profunctor.Optic.Property'.
--
ilens :: (s -> (i , a)) -> (s -> b -> t) -> Ixlens i s t a b
ilens sia sbt = ilensVl $ \iab s -> sbt s <$> uncurry iab (sia s)
{-# INLINE ilens #-}

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

-- | Transform an indexed Van Laarhoven lens into an indexed profunctor 'Lens'.
--
-- An 'Ixlens' is a valid 'Lens' and a valid 'IxTraversal'. 
--
-- Compare 'lensVl' & 'Data.Profunctor.Optic.Traversal.itraversalVl'.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @iabst (const Identity) ≡ Identity@
--
-- * @fmap (iabst $ const f) . (iabst $ const g) ≡ getCompose . iabst (const $ Compose . fmap f . g)@
--
-- More generally, a profunctor optic must be monoidal as a natural 
-- transformation:
-- 
-- * @o id ≡ id@
--
-- * @o ('Data.Profunctor.Composition.Procompose' p q) ≡ 'Data.Profunctor.Composition.Procompose' (o p) (o q)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
ilensVl :: (forall f. Functor f => (i -> a -> f b) -> s -> f t) -> Ixlens i s t a b
ilensVl f = lensVl $ \iab -> f (curry iab) . snd
{-# INLINE ilensVl #-}

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
-- >>> V2 3 1 ^. indexed I21
-- 3
-- >>> V3 "foo" "bar" "baz" & indexed I32 .~ "bip"
-- V3 "foo" "bip" "baz"
--
-- See also 'Data.Profunctor.Optic.Grate.coindexed'.
--
indexed :: F.Representable f => Eq (F.Rep f) => F.Rep f -> Lens' (f a) a
indexed i = lensVl $ lensRep i

---------------------------------------------------------------------
-- Indexed optics 
---------------------------------------------------------------------

-- | TODO: Document
--
-- >>> ilists (ix @Int traversed . ix first' . ix traversed) [("foo",1), ("bar",2)]
-- [(0,'f'),(1,'o'),(2,'o'),(0,'b'),(1,'a'),(2,'r')]
--
-- >>> ilists (ix @Int traversed . ifirst . ix traversed) [("foo",1), ("bar",2)]
-- [(0,'f'),(1,'o'),(2,'o'),(0,'b'),(1,'a'),(2,'r')]
--
-- >>> ilists (ix @Int traversed % ix first' % ix traversed) [("foo",1), ("bar",2)]
-- [(0,'f'),(1,'o'),(2,'o'),(1,'b'),(2,'a'),(3,'r')]
--
-- >>> ilists (ix @Int traversed % ifirst % ix traversed) [("foo",1), ("bar",2)]
-- [(0,'f'),(1,'o'),(2,'o'),(2,'b'),(3,'a'),(4,'r')]
--
ifirst :: Ixlens i (a , c) (b , c) a b
ifirst = lmap assocl . first'

-- | TODO: Document
--
isecond :: Ixlens i (c , a) (c , b) a b
isecond = lmap (\(i, (c, a)) -> (c, (i, a))) . second'

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

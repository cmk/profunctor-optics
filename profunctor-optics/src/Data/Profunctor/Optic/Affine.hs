{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Affine (
    -- * Affine & Ixaffine
    Affine
  , Affine'
  , Ixaffine
  , Ixaffine'
  , affine
  , affine'
  , iaffine
  , iaffine'
  , affineVl
  , iaffineVl
    -- * Optics
  , nulled
  , selected
    -- * Primitive operators
  , withAffine
    -- * Operators
  , matches
    -- * Classes
  , Strong(..)
  , Choice(..)
) where

import Data.Bifunctor (first, second)
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Lens
import Data.Profunctor.Optic.Prism
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Types hiding (branch)

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XFlexibleContexts
-- >>> :set -XTypeApplications
-- >>> :set -XTupleSections
-- >>> :set -XRankNTypes
-- >>> import Data.Maybe
-- >>> import Data.List.NonEmpty (NonEmpty(..))
-- >>> import qualified Data.List.NonEmpty as NE
-- >>> import Data.Functor.Identity
-- >>> import Data.List.Index
-- >>> :load Data.Profunctor.Optic
-- >>> let catchOn :: Int -> Cxprism' Int (Maybe String) String ; catchOn n = kjust $ \k -> if k==n then Just "caught" else Nothing
-- >>> let itraversed :: Ixtraversal Int [a] [b] a b ; itraversed = itraversalVl itraverse

---------------------------------------------------------------------
-- 'Affine' & 'Ixaffine'
---------------------------------------------------------------------

-- | Create a 'Affine' from match and constructor functions.
--
-- /Caution/: In order for the 'Affine' to be well-defined,
-- you must ensure that the input functions satisfy the following
-- properties:
--
-- * @sta (sbt a s) ≡ either (Left . const a) Right (sta s)@
--
-- * @either id (sbt s) (sta s) ≡ s@
--
-- * @sbt (sbt s a1) a2 ≡ sbt s a2@
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
affine :: (s -> t + a) -> (s -> b -> t) -> Affine s t a b
affine sta sbt = dimap (\s -> (s,) <$> sta s) (id ||| uncurry sbt) . right' . second'

-- | Obtain a 'Affine'' from match and constructor functions.
--
affine' :: (s -> Maybe a) -> (s -> a -> s) -> Affine' s a
affine' sa sas = flip affine sas $ \s -> maybe (Left s) Right (sa s)

-- | TODO: Document
--
iaffine :: (s -> t + (i , a)) -> (s -> b -> t) -> Ixaffine i s t a b
iaffine stia sbt = iaffineVl $ \point f s -> either point (fmap (sbt s) . uncurry f) (stia s)

-- | TODO: Document
--
iaffine' :: (s -> Maybe (i , a)) -> (s -> a -> s) -> Ixaffine' i s a
iaffine' sia = iaffine $ \s -> maybe (Left s) Right (sia s) 

-- | Transform a Van Laarhoven 'Affine' into a profunctor 'Affine'.
--
affineVl :: (forall f. Functor f => (forall c. c -> f c) -> (a -> f b) -> s -> f t) -> Affine s t a b
affineVl f = dimap (\s -> (s,) <$> eswap (sat s)) (id ||| uncurry sbt) . right' . second'
  where
    sat = f Right Left
    sbt s b = runIdentity $ f Identity (\_ -> Identity b) s

-- | Transform an indexed Van Laarhoven 'Affine' into an indexed profunctor 'Affine'.
--
iaffineVl :: (forall f. Functor f => (forall c. c -> f c) -> (i -> a -> f b) -> s -> f t) -> Ixaffine i s t a b
iaffineVl f = affineVl $ \cc iab -> f cc (curry iab) . snd

---------------------------------------------------------------------
-- Optics 
---------------------------------------------------------------------

-- | TODO: Document
--
nulled :: Affine' s a
nulled = affine Left const 
{-# INLINE nulled #-}

-- | TODO: Document
--
selected :: (a -> Bool) -> Affine' (a, b) b
selected p = affine (\kv@(k,v) -> branch p kv v k) (\kv@(k,_) v' -> if p k then (k,v') else kv)
{-# INLINE selected #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Test whether the optic matches or not.
--
-- >>> matches just (Just 2)
-- Right 2
--
-- >>> matches just (Nothing :: Maybe Int) :: Either (Maybe Bool) Int
-- Left Nothing
--
matches :: AAffine s t a b -> s -> t + a
matches o = withAffine o $ \sta _ -> sta
{-# INLINE matches #-}

{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Repn where

import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Type

---------------------------------------------------------------------
-- 'Repn' & 'Corepn'
---------------------------------------------------------------------

-- | Obtain a representable profunctor optic from a Van Laarhoven 'Lenslike'.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @abst pure ≡ pure@
--
-- * @fmap (abst f) . abst g ≡ getCompose . abst (Compose . fmap f . g)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
representing :: (forall f. Functor f => (a -> f b) -> s -> f t) -> Repn s t a b
representing abst = tabulate . abst . sieve

-- | Obtain a corepresentable profunctor optic from a Van Laarhoven 'Gratelike'.
--
corepresenting :: (forall f. Functor f => (f a -> b) -> f s -> t) -> Corepn s t a b
corepresenting abst = cotabulate . abst . cosieve

-- | TODO: Document
--
cloneRepn :: Optic (Star (Rep p)) s t a b -> Repnlike p s t a b
cloneRepn o = fromStar . o . toStar

-- | TODO: Document
--
cloneCorepn :: Optic (Costar (Corep p)) s t a b -> Corepnlike p s t a b
cloneCorepn o = fromCostar . o . toCostar 

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | 
--
-- The traversal laws can be stated in terms of 'repnOf':
-- 
-- Identity:
-- 
-- @
-- repnOf t (Identity . f) ≡  Identity (fmap f)
-- @
-- 
-- Composition:
-- 
-- @ 
-- Compose . fmap (repnOf t f) . repnOf t g ≡ repnOf t (Compose . fmap f . g)
-- @
--
-- @
-- repnOf :: Functor f => Lens s t a b -> (a -> f b) -> s -> f t
-- repnOf :: Applicative f => Traversal s t a b -> (a -> f b) -> s -> f t
-- @
--
repnOf :: Applicative f => ATraversal f s t a b -> (a -> f b) -> s -> f t
repnOf o = runStar #. o .# Star
{-# INLINE repnOf #-}

-- | A more permissive variant of 'Data.Profunctor.Optic.Grate.zipWithFOf'.  
--
-- @
-- 'corepnOf' $ 'Data.Profuncto.Optic.Grate.grate' (flip 'Data.Distributive.cotraverse' id) ≡ 'Data.Distributive.cotraverse'
-- @
--
corepnOf :: Functor f => Optic (Costar f) s t a b -> (f a -> b) -> (f s -> t)
corepnOf o = runCostar #. o .# Costar
{-# INLINE corepnOf #-}

---------------------------------------------------------------------
-- Common 'Repn's & 'Corepn's
---------------------------------------------------------------------

-- | A more permissive variant of 'Data.Profunctor.Optic.Grate.closed'. 
--
closed' :: Corepn (c -> a) (c -> b) a b
closed' = corepresenting cotraverse
{-# INLINE closed' #-}

-- | A more permissive variant of 'Data.Profunctor.Optic.Grate.distributed'. 
--
distributed' :: Distributive f => Corepn (f a) (f b) a b
distributed' = corepresenting $ \fab fs -> fmap fab $ distribute fs
{-# INLINE distributed' #-}

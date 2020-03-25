{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Property (
    -- * Iso
    Iso
  , fromto_iso
  , tofrom_iso
    -- * Prism
  , Prism
  , tofrom_prism
  , fromto_prism 
  , idempotent_prism 
    -- * Lens
  , Lens
  , id_lens
  , tofrom_lens
  , fromto_lens
  , idempotent_lens
    -- * Grate
  , Grate
  , id_grate
  , const_grate
  , compose_grate
    -- * Traversal0
  , Traversal0
  , tofrom_traversal0
  , fromto_traversal0
  , idempotent_traversal0
    -- * Traversal
  , Traversal
  , id_traversal
  , id_traversal1
  , pure_traversal
  , compose_traversal
  , compose_traversal1
    -- * Cotraversal
  , Cotraversal
  --, compose_cotraversal
    -- * Setter
  , Setter
  , id_setter
  , compose_setter
  , idempotent_setter
) where 

import Control.Monad as M (join)
import Control.Applicative
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Traversal
import Data.Profunctor.Optic.Setter
import Data.Profunctor.Optic.Lens
import Test.Function.Invertible

---------------------------------------------------------------------
-- 'Iso'
---------------------------------------------------------------------

-- | Going back and forth doesn't change anything.
--
fromto_iso :: Eq s => Iso' s a -> s -> Bool
fromto_iso o s = withIso o $ \sa as -> as (sa s) == s

-- | Going back and forth doesn't change anything.
--
tofrom_iso :: Eq a => Iso' s a -> a -> Bool
tofrom_iso o a = withIso o $ \sa as -> sa (as a) == a

---------------------------------------------------------------------
-- 'Prism'
---------------------------------------------------------------------

-- | If we are able to view an existing focus, then building it will return the original structure.
--
-- * @(id ||| bt) (sta s) ≡ s@
--
tofrom_prism :: Eq s => Prism' s a -> s -> Bool
tofrom_prism o s = withPrism o $ \sta bt -> either id bt (sta s) == s

-- | If we build a whole from a focus, that whole must contain the focus.
--
-- * @sta (bt b) ≡ Right b@
--
fromto_prism :: Eq s => Eq a => Prism' s a -> a -> Bool
fromto_prism o a = withPrism o $ \sta bt -> sta (bt a) == Right a

-- |
--
-- * @left sta (sta s) ≡ left Left (sta s)@
--
idempotent_prism :: Eq s => Eq a => Prism' s a -> s -> Bool
idempotent_prism o s = withPrism o $ \sta _ -> left' sta (sta s) == left' Left (sta s)

---------------------------------------------------------------------
-- 'Lens'
---------------------------------------------------------------------

-- A 'Lens' is a valid 'Traversal' with the following additional laws:

id_lens :: Eq s => Lens' s a -> s -> Bool
id_lens o = M.join invertible $ runIdentity . cloneLensVl o Identity 

-- | You get back what you put in.
--
-- * @view o (set o b a) ≡ b@
--
tofrom_lens :: Eq s => Lens' s a -> s -> Bool
tofrom_lens o s = withLens o $ \sa sas -> sas s (sa s) == s

-- | Putting back what you got doesn't change anything.
--
-- * @set o (view o a) a  ≡ a@
--
fromto_lens :: Eq a => Lens' s a -> s -> a -> Bool
fromto_lens o s a = withLens o $ \sa sas -> sa (sas s a) == a

-- | Setting twice is the same as setting once.
--
-- * @set o c (set o b a) ≡ set o c a@
--
idempotent_lens :: Eq s => Lens' s a -> s -> a -> a -> Bool
idempotent_lens o s a1 a2 = withLens o $ \_ sas -> sas (sas s a1) a2 == sas s a2

---------------------------------------------------------------------
-- 'Grate'
---------------------------------------------------------------------

-- The 'Grate' laws are that of an algebra for the parameterised continuation 'Coindex'.

id_grate :: Eq s => Grate' s a -> s -> Bool
id_grate o = M.join invertible $ cloneGrateVl o runIdentity . Identity 

-- |
--
-- * @sabt ($ s) ≡ s@
--
const_grate :: Eq s => Grate' s a -> s -> Bool
const_grate o s = withGrate o $ \sabt -> sabt ($ s) == s

compose_grate :: Eq s => Functor f => Functor g => Grate' s a -> (f a -> a) -> (g a -> a) -> f (g s) -> Bool
compose_grate o f g = liftA2 (==) lhs rhs
  where lhs = cloneGrateVl o f . fmap (cloneGrateVl o g) 
        rhs = cloneGrateVl o (f . fmap g . getCompose) . Compose

---------------------------------------------------------------------
-- 'Traversal0'
---------------------------------------------------------------------

-- | You get back what you put in.
--
-- * @sta (sbt a s) ≡ either (Left . const a) Right (sta s)@
--
tofrom_traversal0 :: Eq a => Eq s => Traversal0' s a -> s -> a -> Bool
tofrom_traversal0 o s a = withAffine o $ \sta sbt -> sta (sbt s a) == either (Left . flip const a) Right (sta s)

-- | Putting back what you got doesn't change anything.
--
-- * @either id (sbt s) (sta s) ≡ s@
--
fromto_traversal0 :: Eq s => Traversal0' s a -> s -> Bool
fromto_traversal0 o s = withAffine o $ \sta sbt -> either id (sbt s) (sta s) == s

-- | Setting twice is the same as setting once.
--
-- * @sbt (sbt s a1) a2 ≡ sbt s a2@
--
idempotent_traversal0 :: Eq s => Traversal0' s a -> s -> a -> a -> Bool
idempotent_traversal0 o s a1 a2 = withAffine o $ \_ sbt -> sbt (sbt s a1) a2 == sbt s a2

---------------------------------------------------------------------
-- 'Traversal'
---------------------------------------------------------------------

-- A 'Traversal' is a valid 'Setter' with the following additional laws:

id_traversal :: Eq s => Traversal' s a -> s -> Bool
id_traversal o = M.join invertible $ runIdentity . traverses o Identity 

id_traversal1 :: Eq s => Traversal1' s a -> s -> Bool
id_traversal1 o = M.join invertible $ runIdentity . traverses o Identity 

pure_traversal :: Eq (f s) => Applicative f => ATraversal' f s a -> s -> Bool
pure_traversal o = liftA2 (==) (traverses o pure) pure

compose_traversal :: Eq (f (g s)) => Applicative' f => Applicative' g => Traversal' s a -> (a -> g a) -> (a -> f a) -> s -> Bool
compose_traversal o f g = liftA2 (==) lhs rhs
  where lhs = fmap (traverses o f) . traverses o g
        rhs = getCompose . traverses o (Compose . fmap f . g)

compose_traversal1 :: Eq (f (g s)) => Apply f => Apply g => Traversal1' s a -> (a -> g a) -> (a -> f a) -> s -> Bool
compose_traversal1 o f g s = lhs s == rhs s
  where lhs = fmap (traverses o f) . traverses o g
        rhs = getCompose . traverses o (Compose . fmap f . g)

---------------------------------------------------------------------
-- 'Cotraversal'
---------------------------------------------------------------------
{-
-- | A 'Cotraversal' is a valid 'Resetter' with the following additional law:
--
-- * @abst f . fmap (abst g) ≡ abst (f . fmap g . getCompose) . Compose @
--
-- The cotraversal laws can be restated in terms of 'cotraverses1':
--
-- * @cotraverses o (f . runIdentity) ≡  fmap f . runIdentity @
--
-- * @cotraverses o f . fmap (cotraverses o g) == cotraverses o (f . fmap g . getCompose) . Compose@
--
-- See also < https://www.cs.ox.ac.uk/jeremy.gibbons/publications/iterator.pdf >
--
compose_cotraversal :: Eq s => Coapplicative f => Coapplicative g => Cotraversal' s a -> (f a -> a) -> (g a -> a) -> f (g s) -> Bool
compose_cotraversal o f g = liftF2 (==) lhs rhs
  where lhs = cotraverses o f . fmap (cotraverses o g) 
        rhs = cotraverses o (f . fmap g . getCompose) . Compose
-}
---------------------------------------------------------------------
-- 'Setter'
---------------------------------------------------------------------

-- |
--
-- * @over o id ≡ id@
--
id_setter :: Eq s => Setter' s a -> s -> Bool
id_setter o s = over o id s == s

-- |
--
-- * @over o f . over o g ≡ over o (f . g)@
--
compose_setter :: Eq s => Setter' s a -> (a -> a) -> (a -> a) -> s -> Bool
compose_setter o f g s = (over o f . over o g) s == over o (f . g) s

-- |
--
-- * @set o y (set o x a) ≡ set o y a@
--
idempotent_setter :: Eq s => Setter' s a -> s -> a -> a -> Bool
idempotent_setter o s a b = set o b (set o a s) == set o b s

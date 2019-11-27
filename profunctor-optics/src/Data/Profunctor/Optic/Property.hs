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
  , tofrom_lens
  , fromto_lens
  , idempotent_lens
    -- * Grate
  , Grate
  , pure_grate
  , compose_grate
    -- * Traversal0
  , Traversal0
  , tofrom_traversal0
  , fromto_traversal0
  , idempotent_traversal0
    -- * Traversal
  , Traversal
  , pure_traversal
  , compose_traversal
    -- * Cotraversal
  , Cotraversal 
  , pure_cotraversal
  , compose_cotraversal
    -- * Setter
  , Setter
  , pure_setter
  , compose_setter
  , idempotent_setter
) where 

import Control.Applicative
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Iso
--import Data.Profunctor.Optic.View
import Data.Profunctor.Optic.Setter
import Data.Profunctor.Optic.Lens
import Data.Profunctor.Optic.Prism
import Data.Profunctor.Optic.Grate
--import Data.Profunctor.Optic.Fold
import Data.Profunctor.Optic.Traversal

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
idempotent_prism o s = withPrism o $ \sta _ -> left sta (sta s) == left Left (sta s)

---------------------------------------------------------------------
-- 'Lens'
---------------------------------------------------------------------

-- A 'Lens' is a valid 'Traversal' with the following additional laws:

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

-- The 'Grate' laws are that of an algebra for a parameterised continuation monad.

-- |
--
-- * @sabt ($ s) ≡ s@
--
pure_grate :: Eq s => Grate' s a -> s -> Bool
pure_grate o s = withGrate o $ \sabt -> sabt ($ s) == s

-- |
--
-- * @sabt (\k -> h (k . sabt)) ≡ sabt (\k -> h ($ k))@
--
compose_grate :: Eq s => Grate' s a -> ((((s -> a) -> a) -> a) -> a) -> Bool
compose_grate o f = withGrate o $ \sabt -> sabt (\k -> f (k . sabt)) == sabt (\k -> f ($ k))

---------------------------------------------------------------------
-- 'Traversal0'
---------------------------------------------------------------------

-- | You get back what you put in.
--
-- * @sta (sbt a s) ≡ either (Left . const a) Right (sta s)@
--
tofrom_traversal0 :: Eq a => Eq s => Traversal0' s a -> s -> a -> Bool
tofrom_traversal0 o s a = withTraversal0 o $ \sta sbt -> sta (sbt s a) == either (Left . flip const a) Right (sta s)

-- | Putting back what you got doesn't change anything.
--
-- * @either id (sbt s) (sta s) ≡ s@
--
fromto_traversal0 :: Eq s => Traversal0' s a -> s -> Bool
fromto_traversal0 o s = withTraversal0 o $ \sta sbt -> either id (sbt s) (sta s) == s

-- | Setting twice is the same as setting once.
--
-- * @sbt (sbt s a1) a2 ≡ sbt s a2@
--
idempotent_traversal0 :: Eq s => Traversal0' s a -> s -> a -> a -> Bool
idempotent_traversal0 o s a1 a2 = withTraversal0 o $ \_ sbt -> sbt (sbt s a1) a2 == sbt s a2

---------------------------------------------------------------------
-- 'Traversal'
---------------------------------------------------------------------

-- | A 'Traversal' is a valid 'Setter' with the following additional laws:
--
-- * @abst pure ≡ pure@
--
-- * @fmap (abst f) . abst g ≡ getCompose . abst (Compose . fmap f . g)@
--
-- These can be restated in terms of 'traverseOf':
--
-- * @traverseOf abst (Identity . f) ≡  Identity . fmap f@
--
-- * @Compose . fmap (traverseOf abst f) . traverseOf abst g == traverseOf abst (Compose . fmap f . g)@
--
-- See also < https://www.cs.ox.ac.uk/jeremy.gibbons/publications/iterator.pdf >
--
pure_traversal
  :: Eq (f s) 
  => Applicative f
  => ((a -> f a) -> s -> f s)
  -> s -> Bool
pure_traversal abst = liftA2 (==) (abst pure) pure

compose_traversal
  :: Eq (f (g s))
  => Functor f
  => Functor g 
  => (forall f. Functor f => (a -> f a) -> s -> f s) 
  -> (a -> g a) -> (a -> f a) -> s -> Bool
compose_traversal abst f g = liftA2 (==) (fmap (abst f) . abst g)
                                        (getCompose . abst (Compose . fmap f . g))

---------------------------------------------------------------------
-- 'Cotraversal'
---------------------------------------------------------------------

-- | A 'Cotraversal' is a valid 'Resetter' with the following additional laws:
--
-- * @abst extract ≡ extract@
--
-- * @abst f . fmap (abst g) ≡ abst (f . fmap g . getCompose) . Compose @
--
-- These can be restated in terms of 'cotraverseOf':
--
-- * @cotraverseOf abst (f . runIdentity) ≡  fmap f . runIdentity @
--
-- * @cotraverseOf abst f . fmap (cotraverseOf abst g) . getCompose == cotraverseOf abst (f . fmap g . getCompose)@
--
-- See also < https://www.cs.ox.ac.uk/jeremy.gibbons/publications/iterator.pdf >
--
pure_cotraversal
  :: Eq s 
  => Comonad f
  => ((f a -> a) -> f s -> s)
  -> f s -> Bool
pure_cotraversal abst = liftA2 (==) (abst extract) extract

compose_cotraversal
  :: Eq s
  => Functor f 
  => Functor g 
  => (forall f. Functor f => (f a -> a) -> f s -> s) 
  -> (g a -> a) -> (f a -> a) -> g (f s) -> Bool
compose_cotraversal abst f g = liftA2 (==) (abst f . fmap (abst g))
                                          (abst (f . fmap g . getCompose) . Compose)

---------------------------------------------------------------------
-- 'Setter'
---------------------------------------------------------------------

-- |
--
-- * @over o id ≡ id@
--
pure_setter :: Eq s => Setter' s a -> s -> Bool
pure_setter o s = over o id s == s

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

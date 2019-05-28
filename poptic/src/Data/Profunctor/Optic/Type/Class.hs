{-# LANGUAGE UndecidableSuperClasses , GADTs, DataKinds, KindSignatures, TypeFamilies #-}

{-# LANGUAGE TupleSections, FlexibleInstances, ConstraintKinds, PolyKinds, UndecidableInstances #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables,  QuantifiedConstraints#-}

module Data.Profunctor.Optic.Type.Class (
    module Data.Profunctor.Optic.Type.Class
  , module Export
) where

import Data.Profunctor.Optic.Prelude

import Data.Profunctor.Types           as Export
import Data.Profunctor.Choice          as Export 
import Data.Profunctor.Strong          as Export 
import Data.Profunctor.Closed          as Export hiding (Closure)
import Data.Profunctor.Mapping         as Export
import Data.Profunctor.Traversing      as Export


coerce :: (Contravariant f, Functor f) => f a -> f b
coerce = phantom

type IPhantom p = (Bifunctor p, Profunctor p)

class Profunctor p => InPhantom p where
  icoerce :: p a c -> p b c

--instance (Bifunctor p, Profunctor p) => InPhantom p where
--  icoerce = pretagged

instance (Contravariant f, Functor f) => InPhantom (Costar f) where
  icoerce (Costar h) = Costar $ h . coerce

class Profunctor p => OutPhantom p where
  ocoerce :: p c a -> p c b

instance (Contravariant f, Functor f) => OutPhantom (Star f) where
  ocoerce (Star h) = Star $ coerce . h

--instance (forall a. Contravariant (p a), Profunctor p) => OutPhantom p where
--  ocoerce = retagged

instance OutPhantom (Forget f) where
  ocoerce (Forget f) = (Forget f)

cimap :: OutPhantom p => (a -> b) -> (c -> d) -> p b d -> p a c
cimap f _ = lmap f . ocoerce

firstDefault :: OutPhantom p => p a b -> p (a,c) (b,c)
firstDefault = ocoerce . dimap fst id

leftDefault :: InPhantom p => p a b -> p (Either a c) (Either b c)
leftDefault = icoerce . dimap id Left


-- Entailment relationships not already given by 'profunctors':
--class Equalizing (p :: * -> * -> *)
--instance Equalizing p

class (Strong p, Choice p) => AffineTraversing p
instance (Strong p, Choice p) => AffineTraversing p

class (InPhantom p, Choice p) => Reviewing p
instance (InPhantom p, Choice p) => Reviewing p

--class (Bifunctor p, Choice p) => Reviewing p
--instance (Bifunctor p, Choice p) => Reviewing p

--class (Bicontravariant p, Strong p) => Getting p
--instance (Bicontravariant p, Strong p) => Getting p

class (OutPhantom p, Strong p) => Getting p
instance (OutPhantom p, Strong p) => Getting p

class (Getting p, Traversing1 p) => Folding1 p
instance (Getting p, Traversing1 p) => Folding1 p

class (Getting p, Traversing p) => Folding p
instance (Getting p, Traversing p) => Folding p

class (OutPhantom p, Strong p, Choice p) => AffineFolding p
instance (OutPhantom p, Strong p, Choice p) => AffineFolding p

class Strong p => Traversing1 p where
  traverse1' :: Traversable1 f => p a b -> p (f a) (f b)
  wander1 :: (forall f. Apply f => (a -> f b) -> s -> f t) -> p a b -> p s t

instance Apply f => Traversing1 (Star f) where
  traverse1' (Star f) = Star (traverse1 f)
  wander1 f (Star afb) = Star (f afb)

instance Semigroup r => Traversing1 (Forget r) where
  wander1 f (Forget p) = Forget (getConst . f (Const . p))



{-




newtype ProIn p f a b = ProIn { proIn :: p (f a) b }

instance (Profunctor p, Functor f) => Profunctor (ProIn p f) where
  dimap f g (ProIn pab) = ProIn $ dimap (fmap f) g pab

instance (Profunctor p, Phantom f) => Choice (ProIn p f) where
  right' = _RightDefault

_RightDefault :: InPhantom p => p a b -> p (Either c a) (Either c b)
_RightDefault = icoerce . omap Right

instance (Profunctor p, Phantom f) => InPhantom (ProIn p f) where
  icoerce (ProIn pab) = ProIn $ imap coerce pab

newtype ProOut p g a b = ProOut { proOut :: p a (g b) }

instance (Profunctor p, Functor f) => Profunctor (ProOut p f) where
  dimap f g (ProOut pab) = ProOut $ dimap f (fmap g) pab

instance (Profunctor p, Phantom f) => Strong (ProOut p f) where
  second' = _2Default

_2Default :: OutPhantom p => p a b -> p (c, a) (c, b)
_2Default = ocoerce . imap snd

instance (Profunctor p, Phantom f) => OutPhantom (ProOut p f) where
  ocoerce (ProOut pab) = ProOut $ omap coerce pab
-}

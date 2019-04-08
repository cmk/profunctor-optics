{-# LANGUAGE UndecidableSuperClasses, TypeOperators , GADTs, DataKinds, KindSignatures, TypeFamilies #-}

{-# LANGUAGE TupleSections, FlexibleInstances, ConstraintKinds, PolyKinds, UndecidableInstances #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Profunctor.Optic.Types.Class (
    module Data.Profunctor.Optic.Types.Class
  , module Export
) where


import Data.Bifunctor                  as Export
import Data.Bifunctor.Product          as Export
import Data.Functor.Const              as Export
import Data.Functor.Identity           as Export
import Data.Profunctor                 as Export
import Data.Profunctor.Types           as Export
import Data.Profunctor.Choice          as Export (TambaraSum(..))
import Data.Profunctor.Strong          as Export (Tambara(..))
import Data.Profunctor.Closed          as Export hiding (Closure)
import Data.Profunctor.Mapping         as Export
import Data.Profunctor.Traversing      as Export





class Functor f => Phantom f where
  coerce :: f a -> f b

instance Phantom (Const a) where
  coerce (Const a) = Const a



class Choice p => InPhantom p where
  icoerce :: p a c -> p b c

class Strong p => OutPhantom p where
  ocoerce :: p c a -> p c b

instance Phantom f => OutPhantom (Star f) where
  ocoerce (Star h) = Star $ coerce . h

instance OutPhantom (Forget f) where
  ocoerce (Forget f) = (Forget f)

-- Upstream imposes the 'Traversable' requirement.
instance (Phantom f, Traversable f) => InPhantom (Costar f) where
  icoerce (Costar h) = Costar $ h . coerce




-- Entailment relationships not already given by 'profunctors':
class Equalizing (p :: * -> * -> *)
instance Equalizing p

class (Strong p, Choice p) => AffineTraversing p
instance (Strong p, Choice p) => AffineTraversing p

class (InPhantom p, Choice p) => Reviewing p
instance (InPhantom p, Choice p) => Reviewing p

--class (Bifunctor p, Choice p) => Reviewing p
--instance (Bifunctor p, Choice p) => Reviewing p

class (OutPhantom p, Strong p) => Getting p
instance (OutPhantom p, Strong p) => Getting p

--class (Bicontravariant p, Strong p) => Getting p
--instance (Bicontravariant p, Strong p) => Getting p

--class (OutPhantom p, Traversing p) => Folding p

class (OutPhantom p, Traversing p) => Folding p
instance (OutPhantom p, Traversing p) => Folding p

class (OutPhantom p, Choice p, Traversing p) => AffineFolding p
instance (OutPhantom p, Choice p, Traversing p) => AffineFolding p




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

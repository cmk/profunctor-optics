{-# LANGUAGE UndecidableSuperClasses , GADTs, DataKinds, KindSignatures, TypeFamilies #-}

{-# LANGUAGE TupleSections, FlexibleInstances, ConstraintKinds, PolyKinds, UndecidableInstances #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables,  QuantifiedConstraints#-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Data.Profunctor.Optic.Type.Class (
    module Data.Profunctor.Optic.Type.Class
) where

import Control.Comonad (Comonad(..))
import Control.Categorical.Bifunctor hiding (dimap)

import Data.Profunctor.Optic.Prelude hiding (Bifunctor(..), extract)

import Data.Profunctor.Types
import Data.Profunctor.Choice
import Data.Profunctor.Strong
import Data.Profunctor.Closed
import Data.Profunctor.Rep

import qualified Prelude as P
-- Entailment relationships not already given by 'profunctors':
--class Equalizing (p :: * -> * -> *)
--instance Equalizing p

--class (Strong p, Choice p) => AffineTraversing p
--instance (Strong p, Choice p) => AffineTraversing p




-- Orphan instances

instance Cochoice (Forget r) where 
  unleft (Forget adr) = Forget $ adr . Left

instance Comonad f => Strong (Costar f) where
  first' (Costar f) = Costar $ \x -> (f (fmap P.fst x), P.snd (extract x))

  second' (Costar f) = Costar $ \x -> (P.fst (extract x), f (fmap P.snd x))

instance Contravariant f => Contravariant (Star f a) where
  contramap f (Star g) = Star $ contramap f . g

instance {-# OVERLAPPABLE #-} (q ~ p, Profunctor q, Corepresentable q) => Closed p where
  closed = closed'

instance {-# OVERLAPPABLE #-} (Category p, Strong p) => PFunctor (,) p p where 
  first = first'

instance {-# OVERLAPPABLE #-} (Category p, Choice p) => PFunctor Either p p where 
  first = left'

instance {-# OVERLAPPABLE #-} (Category p, Strong p) => QFunctor (,) p p where
  second = second'

instance {-# OVERLAPPABLE #-} (Category p, Choice p) => QFunctor Either p p where
  second = right'

instance {-# OVERLAPPABLE #-} (Category p, Strong p) => Bifunctor (,) p p p where
  bimap f g = f *** g

instance {-# OVERLAPPABLE #-} (Category p, Choice p) => Bifunctor Either p p p where
  bimap f g = f +++ g

instance {-# OVERLAPPABLE #-} (Category p, Strong p) => Braided p (,) where
  braid = arr swp

instance {-# OVERLAPPABLE #-} (Category p, Choice p) => Braided p Either where
  braid = arr coswp

instance {-# OVERLAPPABLE #-} (Category p, Strong p) => Symmetric p (,) where

instance {-# OVERLAPPABLE #-} (Category p, Choice p) => Symmetric p Either where

instance {-# OVERLAPPABLE #-} (Category p, Strong p) => Monoidal p (,) where
  type Id p (,) = ()
  idl = arr P.snd -- p ((),a) a
  idr = arr P.fst
  coidl = arr $ \a -> ((),a) -- p a ((), a)
  coidr = arr $ \a -> (a,())

instance {-# OVERLAPPABLE #-} (Category p, Choice p) => Monoidal p Either where
  type Id p Either = Void
  idl = arr $ either absurd id
  idr = arr $ either id absurd
  coidl = arr Right
  coidr = arr Left

instance {-# OVERLAPPABLE #-} (Category p, Strong p) => Associative p (,) where
  associate = arr $ \((a,b),c) -> (a,(b,c))
  disassociate = arr $ \(a,(b,c)) -> ((a,b),c)

instance {-# OVERLAPPABLE #-} (Category p, Choice p) => Associative p Either where
  associate = arr $ \case
    (Left (Left a)) -> Left a
    (Left (Right b)) -> Right (Left b)
    (Right c) -> Right (Right c)

  disassociate = arr $ \case
    (Left a) -> Left (Left a)
    (Right (Left b)) -> Left (Right b)
    (Right (Right c)) -> Right c

instance {-# OVERLAPPABLE #-} (Category p, Strong p) => Cartesian p where
  type Product p = (,)
  fst = arr P.fst
  snd = arr P.snd -- p (a, b) b
  diag = arr dup
  f &&& g = diag >>> f *** g

instance {-# Incoherent #-} (Category p, Choice p) => CoCartesian p where
  type Sum p = Either
  inl = arr Left
  inr = arr Right
  codiag = arr dedup
  f ||| g = f +++ g >>> codiag

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

import Control.Comonad (Comonad(..))

import Data.Profunctor.Optic.Prelude hiding (extract)

import Data.Profunctor.Types           as Export
import Data.Profunctor.Choice          as Export 
import Data.Profunctor.Strong          as Export 
import Data.Profunctor.Closed          as Export
import Data.Profunctor.Mapping         as Export
import Data.Profunctor.Traversing      as Export


-- Orphan instances
instance Cochoice (Forget r) where 
  unleft (Forget adr) = Forget $ adr . Left

instance Comonad f => Strong (Costar f) where
  first' (Costar f) = Costar $ \x -> (f (fmap fst x), snd (extract x))

  second' (Costar f) = Costar $ \x -> (fst (extract x), f (fmap snd x))

instance Contravariant f => Contravariant (Star f a) where
  contramap f (Star g) = Star $ contramap f . g



-- Entailment relationships not already given by 'profunctors':
--class Equalizing (p :: * -> * -> *)
--instance Equalizing p

--class (Strong p, Choice p) => AffineTraversing p
--instance (Strong p, Choice p) => AffineTraversing p


class Strong p => Traversing1 p where
  traverse1' :: Traversable1 f => p a b -> p (f a) (f b)
  traverse1' = wander1 traverse1

  wander1 :: (forall f. Apply f => (a -> f b) -> s -> f t) -> p a b -> p s t

instance Apply f => Traversing1 (Star f) where
  traverse1' (Star f) = Star (traverse1 f)
  wander1 f (Star afb) = Star (f afb)

instance Semigroup r => Traversing1 (Forget r) where
  wander1 f (Forget p) = Forget (getConst . f (Const . p))





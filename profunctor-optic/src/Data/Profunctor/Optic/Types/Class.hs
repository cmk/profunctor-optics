{-# LANGUAGE UndecidableSuperClasses, TypeOperators , GADTs, DataKinds, KindSignatures, TypeFamilies #-}

{-# LANGUAGE TupleSections, FlexibleInstances, ConstraintKinds, PolyKinds, UndecidableInstances #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Profunctor.Optic.Types.Class (
    module Export
  , module Data.Profunctor.Optic.Types.Class
) where


import Data.Bifunctor                  as Export
import Data.Distributive               as Export
import Data.Tagged                     as Export
import Data.Functor.Const              as Export
import Data.Functor.Identity           as Export
import Data.Profunctor                 as Export
import Data.Profunctor.Types           as Export
import Data.Profunctor.Choice          as Export
import Data.Profunctor.Strong          as Export
import Data.Profunctor.Closed          as Export hiding (Closure)
import Data.Profunctor.Mapping         as Export
import Data.Profunctor.Traversing      as Export
import Data.Profunctor.Composition     as Export



-- Entailment relationships not already given by 'profunctors':
class Equalizing (p :: * -> * -> *)
instance Equalizing p

class (Strong p, Choice p) => AffineTraversing p
instance (Strong p, Choice p) => AffineTraversing p

class (Bifunctor p, Choice p) => Reviewing p
instance (Bifunctor p, Choice p) => Reviewing p

class (Bicontravariant p, Strong p) => Getting p
instance (Bicontravariant p, Strong p) => Getting p

class (Bicontravariant p, Traversing p) => Folding p
instance (Bicontravariant p, Traversing p) => Folding p

class (Bicontravariant p, Choice p, Traversing p) => AffineFolding p
instance (Bicontravariant p, Choice p, Traversing p) => AffineFolding p


class Bicontravariant p where
    cimap :: (b -> a) -> (d -> c) -> p a c -> p b d
    cimap f g = cofirst f . cosecond g

    cofirst :: (b -> a) -> p a c -> p b c
    cofirst f = cimap f id

    cosecond :: (c -> b) -> p a b -> p a c
    cosecond = cimap id

    {-# MINIMAL cimap | (cofirst, cosecond) #-}


instance Bicontravariant (Forget r) where

    cimap f _ (Forget p) = Forget (p . f)




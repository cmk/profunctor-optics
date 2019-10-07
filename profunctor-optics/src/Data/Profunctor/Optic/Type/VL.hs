{-# LANGUAGE UndecidableSuperClasses, TypeOperators , GADTs, DataKinds, KindSignatures, TypeFamilies #-}

{-# LANGUAGE DeriveGeneric #-}
module Data.Profunctor.Optic.Type.VL where

import Data.Profunctor.Optic.Prelude

import           Control.Applicative
import           Data.Bifoldable
import           Data.Bifunctor
import           Data.Bitraversable

type Optic p s t a b = p a b -> p s t

type Optic' p s a = Optic p s s a a

type OverLike f s t a b = (a -> f b) -> s -> f t

type OverLike' f s a = OverLike f s s a a

type Iso s t a b = forall p f. (Profunctor p, Functor f) => p a (f b) -> p s (f t)

type Lens s t a b = forall f. Functor f => OverLike f s t a b

type Prism s t a b = forall p f. (Choice p, Applicative f) => p a (f b) -> p s (f t)

type Traversal s t a b = forall f. Applicative f => OverLike f s t a b

type Fold s a = forall f. (Contravariant f, Applicative f) => OverLike' f s a

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
{-# LANGUAGE FlexibleContexts, AllowAmbiguousTypes#-}

module Data.Profunctor.Optic.Type.Class (
    module Data.Profunctor.Optic.Type.Class
) where


import Control.Comonad (Comonad(..))
import Control.Monad.Fix
import Data.Profunctor.Optic.Prelude

import Data.Functor.Foldable (ListF(..))
import Data.Functor.Base (NonEmptyF(..))
import Data.Functor.Apply
import qualified Prelude as P




-- Orphan instances

instance Cochoice (Forget r) where 
  unleft (Forget adr) = Forget $ adr . Left

instance Comonad f => Strong (Costar f) where
  first' (Costar f) = Costar $ \x -> (f (fmap P.fst x), P.snd (extract x))

  second' (Costar f) = Costar $ \x -> (P.fst (extract x), f (fmap P.snd x))

instance Contravariant f => Contravariant (Star f a) where
  contramap f (Star g) = Star $ contramap f . g

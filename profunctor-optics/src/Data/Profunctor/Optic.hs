{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE DeriveFunctor         #-}
module Data.Profunctor.Optic (
    -- * Optic modules
    module Types
  , module Carrier
  , module Index
  , module Iso
  , module Prism
  , module Lens
  , module Traversal
  , module Fold
  , module View
  , module Setter
  , module Sort
  , module Infix
    -- * Re-exported class hierarchy
  , module Data.Distributive
  , module Control.Coapplicative
  , module Data.Functor.Coapply
  , module Data.Profunctor.Types
  , module Data.Profunctor.Strong
  , module Data.Profunctor.Choice
  , module Data.Profunctor.Closed
  , module Data.Profunctor.Sieve
  , module Data.Profunctor.Rep
  , module Data.Tagged
) where

import Data.Profunctor.Optic.Types            as Types
import Data.Profunctor.Optic.Carrier          as Carrier
import Data.Profunctor.Optic.Index            as Index
import Data.Profunctor.Optic.Iso              as Iso
import Data.Profunctor.Optic.Prism            as Prism
import Data.Profunctor.Optic.Lens             as Lens
import Data.Profunctor.Optic.Traversal        as Traversal
import Data.Profunctor.Optic.Fold             as Fold
import Data.Profunctor.Optic.View             as View
import Data.Profunctor.Optic.Setter           as Setter
import Data.Profunctor.Optic.Sort             as Sort
import Data.Profunctor.Optic.Infix            as Infix

-- Re-exported class hierarchy
import Data.Distributive
import Control.Coapplicative
import Data.Functor.Coapply hiding (apply, branch)
import Data.Profunctor.Types
import Data.Profunctor.Strong (Strong(..), Costrong(..))
import Data.Profunctor.Choice (Choice(..), Cochoice(..))
import Data.Profunctor.Closed (Closed(..))
import Data.Profunctor.Sieve (Sieve(..), Cosieve(..))
import Data.Profunctor.Rep (Representable(..), Corepresentable(..))
import Data.Tagged

{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Either.Optic (
    coswapped
  , coassociated
  , left
  , right
) where

import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Iso
import Data.Profunctor.Optic.Prism

-- | 'Prism' into the `Left` constructor of `Either`.
--
left :: Prism (a + c) (b + c) a b
left = left'

-- | 'Prism' into the `Right` constructor of `Either`.
--
right :: Prism (c + a) (c + b) a b
right = right'

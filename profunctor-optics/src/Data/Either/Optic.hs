{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Either.Optic (
    eswapped
  , eassociated
  , left
  , right
  , coleft
  , coright
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

-- | 'Coprism' out of the `Left` constructor of `Either`.
--
coleft :: Coprism a b (a + c) (b + c)
coleft = unleft

-- | 'Coprism' out of the `Right` constructor of `Either`.
--
coright :: Coprism a b (c + a) (c + b)
coright = unright

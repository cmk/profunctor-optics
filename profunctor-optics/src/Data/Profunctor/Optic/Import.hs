{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}

module Data.Profunctor.Optic.Import (
    between
  , module Export
) where

import Control.Applicative as Export (liftA2, Alternative(..))
import Control.Coapplicative as Export hiding (apply, branch)
import Control.Category as Export hiding ((.), id)
import Control.Monad as Export hiding (void, join)
import Data.Bool as Export
import Data.Distributive as Export
import Data.Foldable as Export (foldr, foldr')
import Data.Function ((&))
import Data.Functor as Export hiding (void, unzip)
import Data.Functor.Apply as Export
import Data.Functor.Coapply as Export hiding (apply, branch, type (+))
import Data.Semigroup.Foldable as Export
import Data.Semigroup.Traversable as Export
import Data.Functor.Compose as Export
import Data.Functor.Const as Export
import Data.Functor.Contravariant as Export
import Data.Functor.Identity as Export
import Data.Monoid as Export
import Data.Profunctor.Unsafe as Export
import Data.Profunctor.Types as Export
import Data.Profunctor.Strong as Export (Strong(..), Costrong(..))
import Data.Profunctor.Choice as Export (Choice(..), Cochoice(..))
import Data.Profunctor.Closed as Export (Closed(..))
import Data.Profunctor.Sieve as Export (Sieve(..), Cosieve(..))
import Data.Profunctor.Rep as Export (Representable(..), Corepresentable(..))
import Data.Tagged as Export
import Data.Bifunctor (Bifunctor(..))
import Data.Void as Export
import Prelude as Export hiding (subtract,sum,product,(^),foldl,foldl1)

-- | Can be used to rewrite
--
-- > \g -> f . g . h
--
-- to
--
-- > between f h
--
between :: (c -> d) -> (a -> b) -> (b -> c) -> a -> d
between f g = (f .) . (. g)
{-# INLINE between #-}

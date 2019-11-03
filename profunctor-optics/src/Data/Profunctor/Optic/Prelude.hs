{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Profunctor.Optic.Prelude (
    module Data.Profunctor.Optic.Prelude
  , module Export
) where

import Control.Arrow as Export ((|||),(&&&),(+++),(***))
import Control.Comonad as Export (Cokleisli(..))
import Control.Applicative as Export
import Control.Category as Export
import Control.Monad as Export hiding (void)
import Control.Comonad as Export
import Data.Bifunctor as Export (Bifunctor (..))
import Data.Distributive as Export
import Data.Functor as Export hiding (void)
import Data.Functor.Compose as Export
import Data.Functor.Const as Export
import Data.Functor.Contravariant as Export hiding (($<), void)
import Data.Functor.Contravariant.Divisible as Export
import Data.Functor.Identity as Export
import Data.Profunctor.Bistar as Export
import Data.Profunctor.Choice as Export
import Data.Profunctor.Closed as Export
import Data.Profunctor.Misc as Export
import Data.Profunctor.Rep as Export
import Data.Profunctor.Sieve as Export
import Data.Profunctor.Strong as Export
import Data.Profunctor.Types as Export hiding (WrappedArrow(..), WrapArrow(..))
import Data.Profunctor.Orphan as Export
import Data.Void as Export
import Prelude as Export hiding (Foldable(..), (.), id, all, any, head, tail)
import qualified Data.Tuple


(&) :: a -> (a -> c) -> c
(&) = flip ($)

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

ustar :: (b -> f c) -> (d -> b) -> Star f d c
ustar f = Star . (f .)

ucostar :: (f d -> b) -> (b -> c) -> Costar f d c
ucostar g = Costar . (. g)

dstar :: (f c -> b) -> Star f a c -> a -> b
dstar f = (f .) . runStar

dcostar :: (a -> f c) -> Costar f c b -> a -> b
dcostar g = (. g) . runCostar

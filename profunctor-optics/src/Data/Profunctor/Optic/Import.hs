{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Profunctor.Optic.Import (
    pliftW
  , pliftF
  , (<<.>>)
  , module Export
) where

import Control.Applicative as Export (liftA2, Alternative(..))
import Control.Category as Export hiding ((.), id)
import Control.Comonad as Export
import Control.Comonad as Export (Cokleisli(..))
import Control.Monad as Export hiding (void, join)
import Data.Distributive as Export
import Data.Function as Export ((&))
import Data.Functor as Export hiding (void)
import Data.Functor.Apply as Export
import Data.Semigroup.Foldable as Export
import Data.Semigroup.Traversable as Export
import Data.Functor.Compose as Export
import Data.Functor.Const as Export
import Data.Functor.Contravariant as Export
import Data.Functor.Contravariant.Divisible as Export
import Data.Functor.Identity as Export
import Data.Profunctor.Arrow as Export ((|||),(&&&),(+++),(***))
import Data.Profunctor.Extra as Export
import Data.Profunctor.Rep as Export
import Data.Profunctor.Sieve as Export
import Data.Profunctor.Types as Export
import Data.Profunctor.Unsafe as Export
import Data.Tagged           as Export
import Data.Void as Export
import Prelude as Export hiding (Foldable(..), all, any, min, max, head, tail, elem, notElem, userError)

pliftW :: Corepresentable p => Monoid (Corep p a) => (b -> c -> d) -> p a b -> p a c -> p a d
pliftW f x y = cotabulate $ liftW2 f (cosieve x) (cosieve y)

pliftF :: Representable p => Apply (Rep p) => (b -> c -> d) -> p a b -> p a c -> p a d
pliftF f x y = tabulate $ \s -> liftF2 f (sieve x s) (sieve y s)

infixl 4 <<.>>

(<<.>>) :: Representable p => Apply (Rep p) => p a (b -> c) -> p a b -> p a c 
(<<.>>) = pliftF ($)

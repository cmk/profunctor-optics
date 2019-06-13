module Orphans where

import Data.Complex
import Control.Applicative
import Numeric.Natural (Natural)



instance Semigroup Bool where

  (<>) = (||)


instance Monoid Bool where

  mempty = False


instance Semigroup a => Semigroup (Complex a) where

  (x :+ y) <> (x' :+ y') = (x <> x') :+ (y <> y')


instance Monoid a => Monoid (Complex a) where

  mempty = mempty :+ mempty


instance Semigroup Natural where

  (<>) = (+)


instance Monoid Natural where

  mempty = 0


instance Monoid e => Alternative (Either e) where

  empty = Left mempty

  (<|>) = (<>)


instance Monoid e => Monoid (Either e a) where

  mempty = Left mempty




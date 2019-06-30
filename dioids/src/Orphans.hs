module Orphans where

import Control.Applicative
import Control.Exception (Exception(..))
import Data.Complex
import Data.Functor.Alt
import Data.Functor.Plus
import Numeric.Natural (Natural)

import P

instance (Exception e1, Exception e2) => Exception (Either e1 e2) where
  toException = either toException toException

  fromException s = (fmap Left $ fromException s) <|> (fmap Right $ fromException s) 


{-
-- Defined in ‘transformers:Control.Monad.Trans.Error’
instance Monoid e => Alternative (Either e) where
  empty = Left mempty

  (<|>) = (<>)
-}

--instance Monoid e => Monoid (Either e a) where mempty = Left mempty

instance Semigroup Word where
  (<>) = (+)


instance Monoid Word where
  mempty = 0


instance Semigroup Int where
  (<>) = (+)


instance Monoid Int where
  mempty = 0


instance Semigroup Bool where
  (<>) = (||)


instance Monoid Bool where
  mempty = False

{-
instance Semigroup a => Semigroup (Complex a) where
  (x :+ y) <> (x' :+ y') = (x <> x') :+ (y <> y')


instance Monoid a => Monoid (Complex a) where
  mempty = mempty :+ mempty
-}

instance Semigroup Natural where
  (<>) = (+)


instance Monoid Natural where
  mempty = 0

{-# LANGUAGE UndecidableInstances #-}

module Data.Profunctor.Tambara where

import Control.Comonad (Comonad(..))

import Data.Profunctor
import Data.Profunctor.Arrow --hiding ((***), (+++), (&&&), (|||), ($$$), pliftA2, pdivide , pchoose, pselect, pdivided)
import Data.Profunctor.Choice
import Data.Profunctor.Closed
import Data.Profunctor.Rep
import Data.Profunctor.Sieve
import Data.Profunctor.Strong hiding (Tambara(..), Cotambara(..))

import Data.Functor.Foldable (ListF(..))
import Data.Functor.Base (NonEmptyF(..))

import Prelude




-- | Right Tambara module parametrized by a tensor.
class Profunctor p => TambaraR (o :: * -> * -> *) p where
  embedr :: p a b -> p (c `o` a) (c `o` b)

-- | Left Tambara module parametrized by a tensor.
class Profunctor p => TambaraL (o :: * -> * -> *) p where
  embedl :: p a b -> p (a `o` c) (b `o` c)

-- Tambara bi-module
type Tambara o p = (TambaraL o p, TambaraR o p)

type Cartesian p = Tambara (,) p

type Cocartesian p = Tambara (+) p

instance Closed p => TambaraR (->) p where
  embedr = closed

--instance Corepresentable p => TambaraR (->) p where embedr = closed'

instance Strong p => TambaraL (,) p where
  embedl = first'

instance Strong p => TambaraR (,) p where
  embedr = second'

instance Choice p => TambaraL (+) p where
  embedl = left'

instance Choice p => TambaraR (+) p where
  embedr = right'

class Profunctor p => CotambaraL (o :: * -> * -> *) p where
  projectl :: p (a `o` c) (b `o` c) -> p a b

-- | 
--
-- @ projectl . embedl == id @
-- @ projectr . embedr == id @
--
class Profunctor p => CotambaraR (o :: * -> * -> *) p where
  projectr :: p (c `o` a) (c `o` b) -> p a b

-- Cotambara bi-module
type Cotambara t p = (CotambaraL t p, CotambaraR t p)

instance Costrong p => CotambaraL (,) p where
  projectl = unfirst

instance Costrong p => CotambaraR (,) p where
  projectr = unsecond

instance Cochoice p => CotambaraL (+) p where
  projectl = unleft

instance Cochoice p => CotambaraR (+) p where
  projectr = unright

toListF :: () + (a , b) -> ListF a b
toListF (Left ()) = Nil
toListF (Right (a, b)) = Cons a b

fromListF :: ListF a b -> () + (a , b)
fromListF Nil = Left ()
fromListF (Cons a b) = Right (a, b)

fromNonEmptyF :: NonEmptyF a b -> (a , () + b)
fromNonEmptyF (NonEmptyF a mb) = 
  case mb of
    Nothing -> (a, Left ())
    Just b -> (a, Right b)

toNonEmptyF :: (a , () + b) -> NonEmptyF a b
toNonEmptyF (a, mb) =
  case mb of
    Left _ -> NonEmptyF a Nothing
    Right b -> NonEmptyF a (Just b)

instance (Profunctor p, Cartesian p) => TambaraL NonEmptyF p where
  embedl = dimap fromNonEmptyF toNonEmptyF . embedl @(,)

instance (Profunctor p, Cartesian p, Cocartesian p) => TambaraR NonEmptyF p where
  embedr = dimap fromNonEmptyF toNonEmptyF . embedr @(,) . embedr @(+)


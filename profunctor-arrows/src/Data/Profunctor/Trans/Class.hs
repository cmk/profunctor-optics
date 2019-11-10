{-# LANGUAGE ExistentialQuantification, DefaultSignatures, UndecidableInstances #-}

module Data.Profunctor.Trans.Class where

import Data.Profunctor
import Data.Profunctor.Misc
import Data.Profunctor.Choice
import Data.Profunctor.Closed
import Data.Profunctor.Strong
import Data.Profunctor.Traversing
import Data.Profunctor.Mapping
import Data.Profunctor.Monad
import Data.Profunctor.Yoneda
import Prelude

import Data.Kind
import Data.Profunctor.Unsafe
--import Data.Tagged
import Data.Void

--import Control.Applicative.Backwards (Backwards(..))
import Data.Functor.Identity (Identity(..))
import Data.Functor.Compose (Compose(..))

--type Identical t = (Monad t, Comonad t)
class (Traversable f, Applicative f) => Identical f where
  extract :: f a -> a

instance Identical Identity where
  extract (Identity x) = x

--instance Identical f => Identical (Backwards f) where extract (Backwards x) = extract x

instance (Identical f, Identical g) => Identical (Compose f g) where
  extract (Compose x) = extract (extract x)


-- see also http://hackage.haskell.org/package/mmorph-1.1.3/docs/Control-Monad-Morph.html

-- | The class of profunctor transformers.
--
-- Instances should satisfy the following laws:
--
-- * @trans id ≡ id@
--
-- * @trans ('Data.Profunctor.Composition.Procompose' p q) ≡ 'Data.Profunctor.Composition.Procompose' (trans p) (trans q)*
--
-- See <https://www.cs.ox.ac.uk/jeremy.gibbons/publications/proyo.pdf> Section 4.5.
--
class ProfunctorFunctor t => ProfunctorTrans t where
  type Sigma t :: (* -> *) -> Constraint
  type Theta t :: (* -> * -> *) -> Constraint
  
  plift :: p a b -> t p a b
  default plift :: ProfunctorMonad t => Profunctor p => p a b -> t p a b
  plift = proreturn

  trans :: Sigma t s => t p a b -> t p (s a) (s b)

instance (forall p. Profunctor p) => ProfunctorTrans Coyoneda where
  type Sigma Coyoneda = Identical

  plift = Coyoneda id id

  trans = dimap extract pure

instance (forall p. Profunctor p) => ProfunctorTrans FreeTraversing where
  type Sigma FreeTraversing = Traversable

  trans = traverse'

instance (forall p. Profunctor p) => ProfunctorTrans FreeMapping where
  type Sigma FreeMapping = Functor

  trans = map'

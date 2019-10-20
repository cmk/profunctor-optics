module Data.Profunctor.Bistar where

import Control.Applicative hiding (WrappedArrow(..))
import Control.Arrow
import Control.Comonad
import Control.Comonad.Cofree (Cofree(..))
import Control.Monad (MonadPlus(..), (>=>))
import Control.Monad.Free (Free(..))
import Data.Distributive
import Data.Foldable
import Data.Functor.Contravariant
import Data.Functor.Foldable
import Data.Functor.Identity
import Data.Monoid hiding (PSemigroup)
import Data.Profunctor.Types
import Data.Traversable
import Prelude

import Data.Profunctor.Task

newtype Bistar f g a b = Bistar { runBistar :: g a -> f b }

instance Functor f => Functor (Bistar f g a) where
  fmap k (Bistar f) = Bistar (fmap k . f)
  {-# INLINE fmap #-}

instance Contravariant f => Contravariant (Bistar f g a) where
  contramap f (Bistar g) = Bistar (contramap f . g)
  {-# INLINE contramap #-}

instance (Functor f, Functor g) => Profunctor (Bistar f g) where
  dimap ab cd (Bistar bfc) = Bistar (fmap cd . bfc . fmap ab)
  {-# INLINE dimap #-}
  lmap k (Bistar f) = Bistar (f . fmap k)
  {-# INLINE lmap #-}
  rmap = fmap
  {-# INLINE rmap #-}

instance Applicative f => Applicative (Bistar f g a) where
  pure a = Bistar $ \_ -> pure a
  Bistar ff <*> Bistar fx = Bistar $ \a -> ff a <*> fx a
  Bistar ff  *> Bistar fx = Bistar $ \a -> ff a  *> fx a
  Bistar ff <*  Bistar fx = Bistar $ \a -> ff a <*  fx a

instance Alternative f => Alternative (Bistar f g a) where
  empty = Bistar $ \_ -> empty
  Bistar f <|> Bistar g = Bistar $ \a -> f a <|> g a

instance Monad f => Monad (Bistar f g a) where
  return a = Bistar $ \_ -> return a
  Bistar m >>= f = Bistar $ \ e -> do
    a <- m e
    runBistar (f a) e

instance MonadPlus f => MonadPlus (Bistar f g a) where
  mzero = Bistar $ \_ -> mzero
  Bistar f `mplus` Bistar g = Bistar $ \a -> f a `mplus` g a

extractPair :: (forall f g. (Functor f, Functor g) => (g a -> f b) -> g s -> f t) -> (s -> a, b -> t)
extractPair l = (getConst . (l (Const . runIdentity)) . Identity, runIdentity . (l (Identity . getConst)) . Const)

extractPair' :: (((s -> a) -> Store (s -> a) b b) -> (s -> s) -> Store (s -> a) b t) -> (s -> a, b -> t)
extractPair' l = (f, g) where Store g f = l (Store id) id


lowerStar :: Bistar f Identity a b -> Star f a b
lowerStar = Star . (. Identity) . runBistar

lowerStar' :: Bistar f g a b -> Star f (g a) b
lowerStar' = Star . runBistar 

lowerCostar :: Bistar Identity g a b -> Costar g a b
lowerCostar = Costar . (runIdentity .) . runBistar

lowerCostar' :: Bistar f g a b -> Costar g a (f b)
lowerCostar' = Costar . runBistar

bicata :: Functor f => Bistar Identity f (Identity a) (f a)
bicata = Bistar distCata

biana :: Functor f => Bistar f Identity (f a) (Identity a)
biana = Bistar distAna

biapo :: Recursive t => Bistar (Base t) (Either t) (Base t a) (Either t a)
biapo = Bistar distApo

bipara :: Corecursive t => Bistar ((,) t) (Base t) (t , a) (Base t a)
bipara = Bistar distPara

bihisto :: Functor f => Bistar (Cofree f) f (Cofree f a) (f a)
bihisto = Bistar distHisto

bifutu :: Functor f => Bistar f (Free f) (f a) (Free f a)
bifutu = Bistar distFutu

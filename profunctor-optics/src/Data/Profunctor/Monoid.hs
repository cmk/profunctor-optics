{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Profunctor.Monoid where

import Control.Arrow ((^>>))
import Control.Monad
import Control.Category (Category, (>>>), (<<<))
import Control.Comonad
import Data.Bifunctor
import Data.Bifunctor.Swap
import Data.Functor.Apply

import Data.Profunctor
import Data.Profunctor.Arrow hiding ((***), (+++), (&&&), (|||), ($$$), pliftA2, pdivide , pchoose, pselect, pdivided)
import Data.Profunctor.Choice
import Data.Profunctor.Closed
import Data.Profunctor.Rep
import Data.Profunctor.Sieve
import Data.Profunctor.Strong hiding (Tambara(..), Cotambara(..))
import Data.Void

import Data.Functor.Contravariant.Divisible

import Prelude

-- | Tensor pappenducts.
--
class Profunctor p => PSemigroup (o :: * -> * -> *) p where
  pappend :: p a1 b1 -> p a2 b2 -> p (a1 `o` a2) (b1 `o` b2)

{-
-- | Profunctor equivalent of 'liftA2'.
--
pliftA2 :: PSemigroup (,) p => ((b1 , b2) -> b) -> p a b1 -> p a b2 -> p a b
pliftA2 f x y = dimap dup f $ x *** y

-- | TODO: Document
--
pstrong :: PSemigroup (,) p => p a b1 -> p a b2 -> p a (b1 , b2) 
pstrong = pliftA2 id

-- | Profunctor equivalent of 'Data.Functor.Divisible.divide'.
--
pdivide :: PSemigroup (,) p => (a -> (a1 , a2)) -> p a1 b -> p a2 b -> p a b
pdivide f x y = dimap f fst $ x *** y

-- | Profunctor equivalent of 'Data.Functor.Divisible.divided'.
--
pdivide' :: PSemigroup (,) p => p a1 b -> p a2 b -> p (a1 , a2) b
pdivide' = pdivide id
-}
-- | Profunctor equivalent of 'Data.Functor.Divisible.choose'.
--
pchoose :: PSemigroup (+) p => (a -> (a1 + a2)) -> p a1 b -> p a2 b -> p a b
pchoose f x y = dimap f dedup $ x +++ y

-- | TODO: Document
--
pchoice :: PSemigroup (+) p => p a1 b -> p a2 b -> p (a1 + a2) b
pchoice = pchoose id 

-- | TODO: Document
--
pselect :: PSemigroup (+) p => ((b1 + b2) -> b) -> p a b1 -> p a b2 -> p a b
pselect f x y = dimap Left f $ x +++ y

-- | TODO: Document
--
pselect' :: PSemigroup (+) p => p a b1 -> p a b2 -> p a (b1 + b2)
pselect' = pselect id

{-
infixr 3 ***

-- | TODO: Document
--
-- @p <*> x ≡ dimap dup eval (p *** x)@
--
(***) :: PSemigroup (,) p => p a1 b1 -> p a2 b2 -> p (a1 , a2) (b1 , b2)
(***) = pappend

infixr 3 &&&

-- | TODO: Document
--
(&&&) :: PSemigroup (,) p => p a b1 -> p a b2 -> p a (b1 , b2)
(&&&) = pstrong
-}
infixr 2 +++

-- | TODO: Document
--
(+++) :: PSemigroup (+) p => p a1 b1 -> p a2 b2 -> p (a1 + a2) (b1 + b2)
(+++) = pappend

infixr 2 |||

-- | TODO: Document
--
(|||) :: PSemigroup (+) p => p a1 b -> p a2 b -> p (a1 + a2) b
(|||) = pchoice

--tagall :: PMonoid (+) p => Bifunctor p => p a b
--tagall = lcoerce $ rmap absurd $ punit @(+)

--instance (Profunctor p, (forall a. Applicative (p a))) => PSemigroup (,) p where pappend f g = dimap fst (,) f <*> lmap snd g
--instance (Profunctor p, (forall a. Apply (p a))) => PSemigroup (,) p where pappend f g = dimap fst (,) f <.> lmap snd g

--instance (Profunctor p, (forall a. Divisible (p a))) => PSemigroup (+) p where

instance PSemigroup (+) (->) where
  pappend f _ (Left x)  = Left (f x)
  pappend _ g (Right y) = Right (g y)

instance Functor f => PSemigroup (+) (Star f) where
  pappend (Star f) (Star g) = Star $ \case 
       Left  x -> Left <$> f x
       Right y -> Right <$> g y

instance Comonad w => PSemigroup (+) (Cokleisli w) where
  pappend (Cokleisli f) (Cokleisli g) =
      (\ a -> Left  . f . (a <$)) |||
      (\ a -> Right . g . (a <$)) ^>> Cokleisli (extract <*> void)

type family Id (o :: * -> * -> *) :: *
type instance Id (,) = ()
type instance Id (+) = Void

-- https://ncatlab.org/nlab/show/monoidal+category
class PSemigroup o p => PMonoid o p where
  punit :: p (Id o) (Id o)

instance (PSemigroup (,) p, (forall a. Applicative (p a))) => PMonoid (,) p where
  punit = pure ()

instance (PSemigroup (+) p, (forall a. Divisible (p a))) => PMonoid (+) p where
  punit = conquer

{-
pabsurd :: PMonoid (+) p => p Void a
pabsurd = rmap absurd $ punit @(+)

ppure :: PMonoid (,) p => b -> p a b
ppure b = dimap (const ()) (const b) $ punit @(,)
-}

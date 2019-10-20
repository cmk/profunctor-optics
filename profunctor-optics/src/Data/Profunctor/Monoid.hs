{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Profunctor.Monoid where

import Control.Category (Category, (>>>), (<<<))
import Control.Comonad (Comonad(..))

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

-- | Tensor products.
--
class Profunctor p => PSemigroup (o :: * -> * -> *) p where
  prod :: p a1 b1 -> p a2 b2 -> p (a1 `o` a2) (b1 `o` b2)

-- | Profunctor equivalent of 'liftA2'.
--
pliftA2 :: PSemigroup (,) p => ((b1 , b2) -> b) -> p a b1 -> p a b2 -> p a b
pliftA2 f x y = dimap dup f $ x *** y

-- | Profunctor equivalent of 'Data.Functor.Divisible.divide'.
--
pdivide :: PSemigroup (,) p => (a -> (a1 , a2)) -> p a1 b -> p a2 b -> p a b
pdivide f x y = dimap f fst $ x *** y

-- | TODO: Document
--
pselect :: PSemigroup (+) p => ((b1 + b2) -> b) -> p a b1 -> p a b2 -> p a b
pselect f x y = dimap Left f $ x +++ y

-- | Profunctor equivalent of 'Data.Functor.Divisible.choose'.
--
pchoose :: PSemigroup (+) p => (a -> (a1 + a2)) -> p a1 b -> p a2 b -> p a b
pchoose f x y = dimap f dedup $ x +++ y

infixr 3 ***

-- | TODO: Document
--
(***) :: PSemigroup (,) p => p a1 b1 -> p a2 b2 -> p (a1 , a2) (b1 , b2)
(***) = prod

infixr 2 +++

-- | TODO: Document
--
(+++) :: PSemigroup (+) p => p a1 b1 -> p a2 b2 -> p (a1 + a2) (b1 + b2)
(+++) = prod

infixr 3 &&&

-- | TODO: Document
--
(&&&) :: PSemigroup (,) p => p a b1 -> p a b2 -> p a (b1 , b2)
x &&& y = pliftA2 id x y

infixr 2 |||

-- | TODO: Document
--
(|||) :: PSemigroup (+) p => p a1 b -> p a2 b -> p (a1 + a2) b
x ||| y = pchoose id x y

infixr 0 $$$

-- | Profunctor equivalent of '<*>'.
--
($$$) :: PSemigroup (,) p => p a (b -> c) -> p a b -> p a c
($$$) f x = dimap dup eval (f *** x)

-- | Profunctor equivalent of 'Data.Functor.Divisible.divided'.
--
pdivided :: PSemigroup (,) p => p a1 b -> p a2 b -> p (a1 , a2) b
pdivided = pdivide id

--TODO: use Apply
instance (Profunctor p, (forall a. Applicative (p a))) => PSemigroup (,) p where prod f g = dimap fst (,) f <*> lmap snd g
--instance (Profunctor p, (forall a. Apply (p a))) => PSemigroup (,) p where prod f g = dimap fst (,) f <.> lmap snd g

--TODO: add instances to Flip and uncomment
--instance (Profunctor p, (forall a. Decidable (Flip p a))) => PSemigroup (+) p where prod f g = runFlip $ Flip (rmap Left f) >+< Flip (rmap Right g)

--instance Applicative f => PSemigroup (,) (Star f) where prod (Star f) (Star g) = Star $ \ (x, y) -> pure (,) <*> (f x) <*> (g y)

--instance (Profunctor p, (forall a. Divisible (p a))) => PSemigroup (+) p where prod f g = dimap fst (,) f <*> lmap snd g


--chosen :: Decidable f => p a b -> p a c -> f a (Either b c)
--(>+<) :: Decidable f => f a -> f b -> f (a + b)

{-
λ> :t choice id
choice id :: Choice p => p b a -> p (a + b) a
λ> :t choice coswp

choice coswp :: Choice p => p b1 a1 -> p (b1 + a1) a1

choice coswp :: Choice p => p b2 a2 -> p (b2 + a2) a2

mine :: Profunctor p => p a1 b1 -> p a2 b2 -> p (a1 + a2) (b1 + b2)
mine f g = rmap _ g `papply` dimap (,) Left f 
-}





--foob f g = (choice id f) >+< (choice id g)

instance Functor f => PSemigroup (+) (Star f) where
  prod (Star f) (Star g) = Star $ \case 
       Left  x -> Left <$> f x
       Right y -> Right <$> g y


--instance PSemigroup (,) (->) where prod f g (x, y) = (f x, g y)
instance PSemigroup (+) (->) where
  prod f _ (Left x)  = Left (f x)
  prod _ g (Right y) = Right (g y)

{-

instance Comonad ɯ => PSemigroup (+) (Cokleisli ɯ) where
  prod (Cokleisli f) (Cokleisli g) =
      (\ a -> Left  . f . (a <$)) |||
      (\ a -> Right . g . (a <$)) ^>> Cokleisli (extract <*> void)

void = error "TODO"
-}

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

pabsurd :: PMonoid (+) p => p Void a
pabsurd = rmap absurd $ punit @(+)

ppure :: PMonoid (,) p => b -> p a b
ppure b = dimap (const ()) (const b) $ punit @(,)

{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Profunctor.Product where

import Control.Category (Category, (>>>), (<<<))
import Control.Comonad (Comonad(..))

import Data.Bifunctor.Swap
import Data.Functor.Apply

import Data.Profunctor
import Data.Profunctor.Arrow hiding ((***), (+++), (&&&), (|||), ($$$), pliftA2, pdivide , pchoose, pselect, pdivided)
import Data.Profunctor.Choice
import Data.Profunctor.Closed
import Data.Profunctor.Rep
import Data.Profunctor.Sieve
import Data.Profunctor.Strong hiding (Tambara(..), Cotambara(..))
import Data.Profunctor.Tambara
import Data.Void

import Prelude


-- | Tensor products.
--
class Profunctor p => Product (o :: * -> * -> *) p where
  prod :: p a₁ b₁ -> p a₂ b₂ -> p (a₁ `o` a₂) (b₁ `o` b₂)

-- | TODO: Document
--
prodl :: (Category p, TambaraL o p, Swap o) => p a₁ b₁ -> p a₂ b₂ -> p (a₁ `o` a₂) (b₁ `o` b₂)
prodl f g = embedl f >>> arr swap >>> embedl g >>> arr swap

-- | TODO: Document
--
prodr :: (Category p, TambaraR o p, Swap o) => p a₁ b₁ -> p a₂ b₂ -> p (a₁ `o` a₂) (b₁ `o` b₂)
prodr f g = embedr g >>> arr swap >>> embedr f >>> arr swap

-- | Profunctor equivalent of 'liftA2'.
--
pliftA2 :: Product (,) p => ((b₁ , b₂) -> b) -> p a b₁ -> p a b₂ -> p a b
pliftA2 f x y = dimap dup f $ x *** y

-- | Profunctor equivalent of 'Data.Functor.Divisible.divide'.
--
pdivide :: Product (,) p => (a -> (a₁ , a₂)) -> p a₁ b -> p a₂ b -> p a b
pdivide f x y = dimap f fst $ x *** y

-- | Profunctor equivalent of 'Data.Functor.Divisible.choose'.
--
pchoose :: Product (+) p => (a -> (a₁ + a₂)) -> p a₁ b -> p a₂ b -> p a b
pchoose f x y = dimap f dedup $ x +++ y

-- | TODO: Document
--
pselect :: Product (+) p => ((b₁ + b₂) -> b) -> p a b₁ -> p a b₂ -> p a b
pselect f x y = dimap Left f $ x +++ y

infixr 3 ***

-- | TODO: Document
--
(***) :: Product (,) p => p a₁ b₁ -> p a₂ b₂ -> p (a₁ , a₂) (b₁ , b₂)
(***) = prod

infixr 2 +++

-- | TODO: Document
--
(+++) :: Product (+) p => p a₁ b₁ -> p a₂ b₂ -> p (a₁ + a₂) (b₁ + b₂)
(+++) = prod

infixr 3 &&&

-- | TODO: Document
--
(&&&) :: Product (,) p => p a b₁ -> p a b₂ -> p a (b₁ , b₂)
x &&& y = pliftA2 id x y

infixr 2 |||

-- | TODO: Document
--
(|||) :: Product (+) p => p a₁ b -> p a₂ b -> p (a₁ + a₂) b
x ||| y = pchoose id x y

infixr 0 $$$

-- | Profunctor equivalent of '<*>'.
--
($$$) :: Product (,) p => p a (b -> c) -> p a b -> p a c
($$$) f x = dimap dup eval (f *** x)

-- | Profunctor equivalent of 'Data.Functor.Divisible.divided'.
--
pdivided :: Product (,) p => p a₁ b -> p a₂ b -> p (a₁, a₂) b
pdivided = pdivide id


instance (Profunctor p, (forall a. Apply (p a))) => Product (,) p where
  prod f g = dimap fst (,) f <.> lmap snd g


--TODO: add instances to Flip and uncomment
--instance (Profunctor p, (forall a. Decidable (Flip p a))) => Product (+) p where prod f g = runFlip $ Flip (rmap Left f) >+< Flip (rmap Right g)



-- instance Decidable f => PDecidable (Costar f) where
-- instance Decidable f => f ~ Corep p => PDecidable p where

instance Applicative f => Product (,) (Star f) where
  prod (Star f) (Star g) = Star $ \ (x, y) -> pure (,) <*> (f x) <*> (g y)

instance Functor f => Product (+) (Star f) where
  prod (Star f) (Star g) = Star $ \case 
       Left  x -> Left <$> f x
       Right y -> Right <$> g y


--instance Product (,) (->) where prod f g (x, y) = (f x, g y)
instance Product (+) (->) where
  prod f _ (Left x)  = Left (f x)
  prod _ g (Right y) = Right (g y)


{-

instance Comonad ɯ => Product (+) (Cokleisli ɯ) where
  prod (Cokleisli f) (Cokleisli g) =
      (\ a -> Left  . f . (a <$)) |||
      (\ a -> Right . g . (a <$)) ^>> Cokleisli (extract <*> void)

void = error "TODO"
-}

type family Id (o :: * -> * -> *) :: *
type instance Id (,) = ()
type instance Id (+) = Void

-- https://ncatlab.org/nlab/show/monoidal+category
class Product o p => Monoidal o p where
  punit :: p (Id o) (Id o)

instance (Profunctor p, (forall a. Apply (p a)), (forall a. Applicative (p a))) => Monoidal (,) p where
  punit = pure ()

ppure :: Monoidal (,) p => b -> p a b
ppure b = dimap (const ()) (const b) $ punit @(,)

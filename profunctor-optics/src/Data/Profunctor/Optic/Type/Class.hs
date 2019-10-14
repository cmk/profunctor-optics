{-# LANGUAGE UndecidableSuperClasses , GADTs, DataKinds, KindSignatures, TypeFamilies #-}

{-# LANGUAGE TupleSections, FlexibleInstances, ConstraintKinds, PolyKinds, UndecidableInstances #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables,  QuantifiedConstraints#-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Data.Profunctor.Optic.Type.Class (
    module Data.Profunctor.Optic.Type.Class
) where

import Control.Comonad (Comonad(..))
import Control.Monad.Fix
import Data.Profunctor.Optic.Prelude

import Data.Functor.Foldable (ListF(..))
import Data.Functor.Base (NonEmptyF(..))
import Data.Functor.Apply
import qualified Prelude as P


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

{-
instance TambaraL NonEmptyF (->) where
  embedl = dimap fromNonEmptyF toNonEmptyF . first'

instance TambaraR NonEmptyF (->) where
  embedr = dimap fromNonEmptyF toNonEmptyF . second' . right'
-}

newtype Upsert a b = Upsert { runUpsert :: Maybe a -> b }

instance Profunctor Upsert where
  dimap f g (Upsert ab) = Upsert (g . ab . fmap f)

instance TambaraL NonEmptyF Upsert where
   embedl (Upsert mab) = Upsert $ \x -> case x of
        Nothing      -> NonEmptyF (mab Nothing) Nothing
        Just (NonEmptyF a mb) -> NonEmptyF (mab $ Just a) mb


-- Or use Product / Coproduct
-- class (forall a. Apply (p a)) => Proapply p where
-- ($$$) :: Product (,) p => p a (b -> c) -> p a b -> p a c

-- class (forall a. Applicative (p a)) => Proapplicative p where
--  ppure :: b -> p a b
--  ppure b = dimap (const ()) (const b) punit

--  punit  :: p () ()
--  punit = ppure () 

-- Tensor products
class Profunctor p => Product (o :: * -> * -> *) p where
  prod :: p a₁ b₁ -> p a₂ b₂ -> p (a₁ `o` a₂) (b₁ `o` b₂)

infixr 3 ***, &&&

(***) :: Product (,) p => p a₁ b₁ -> p a₂ b₂ -> p (a₁ , a₂) (b₁ , b₂)
(***) = prod

(&&&) :: Product (,) p => p a b₁ -> p a b₂ -> p a (b₁ , b₂)
f &&& g = f *** g <<^ dup 

infixr 0 $$$

($$$) :: Product (,) p => p a (b -> c) -> p a b -> p a c
($$$) f x = dimap dup eval (f *** x)

infixr 2 +++, |||

(+++) :: Product (+) p => p a₁ b₁ -> p a₂ b₂ -> p (a₁ + a₂) (b₁ + b₂)
(+++) = prod

(|||) :: Product (+) p => p a₁ b -> p a₂ b -> p (a₁ + a₂) b
f ||| g = dedup ^<< f +++ g


papply :: Product (,) p => p a (b -> c) -> p a b -> p a c
papply f x = dimap dup eval (f *** x)

prod' :: (Category p, TambaraL o p, Swap o) => p a₁ b₁ -> p a₂ b₂ -> p (a₁ `o` a₂) (b₁ `o` b₂)-- (a `ten` c) (b1 `ten` b2)
prod' f g = embedl f >>> arr swap >>> embedl g >>> arr swap


--instance (Profunctor p, Tambara (,) p, Category p) => Product (,) p where prod f g = embedl f >>> arr swap >>> embedl g >>> arr swap

instance (Profunctor p, (forall a. Apply (p a))) => Product (,) p where
  prod f g = (,) `rmap` lmap fst f <.> lmap snd g

--TODO: add instances to Flip and uncomment
--instance (Profunctor p, (forall a. Decidable (Flip p a))) => Product (+) p where
--  prod f g = unFlip $ Flip (rmap Left f) >+< Flip (rmap Right g)

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

-- https://ncatlab.org/nlab/show/monoidal+category
class Profunctor p => Pointed p where
  ppure :: b -> p a b
  ppure b = dimap (const ()) (const b) punit

  punit :: p () ()
  punit = ppure ()

instance (Profunctor p, (forall a. Applicative (p a))) => Pointed p where
  ppure = pure

-- Orphan instances

instance Cochoice (Forget r) where 
  unleft (Forget adr) = Forget $ adr . Left

instance Comonad f => Strong (Costar f) where
  first' (Costar f) = Costar $ \x -> (f (fmap P.fst x), P.snd (extract x))

  second' (Costar f) = Costar $ \x -> (P.fst (extract x), f (fmap P.snd x))

instance Contravariant f => Contravariant (Star f a) where
  contramap f (Star g) = Star $ contramap f . g

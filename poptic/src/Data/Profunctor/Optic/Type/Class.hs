{-# LANGUAGE UndecidableSuperClasses, TypeOperators , GADTs, DataKinds, KindSignatures, TypeFamilies #-}

{-# LANGUAGE TupleSections, FlexibleInstances, ConstraintKinds, PolyKinds, UndecidableInstances #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Profunctor.Optic.Type.Class (
    module Data.Profunctor.Optic.Type.Class
  , module Export
) where

import Data.Profunctor.Optic.Prelude

import Data.Profunctor.Types           as Export
import Data.Profunctor.Choice          as Export 
import Data.Profunctor.Strong          as Export 
import Data.Profunctor.Closed          as Export hiding (Closure)
import Data.Profunctor.Mapping         as Export
import Data.Profunctor.Traversing      as Export



import Data.Bifunctor (Bifunctor (..))
import Data.Bifunctor.Flip (Flip (..))
import Data.Bifunctor.Product (Product (..))
import Data.Bifunctor.Sum (Sum (..))
import Data.Bifunctor.Tannen (Tannen (..))
import Data.Bifunctor.Biff (Biff (..))
import Data.Either.Validation (Validation(..))

import qualified Data.Tuple

-- | Symmetric 'Bifunctor's.
--
-- @
-- 'swap' . 'swap' = 'id'
-- @
--
-- If @p@ is a 'Bifunctor' the following property is assumed to hold:
--
-- @
-- 'swap' . 'bimap' f g = 'bimap' g f . 'swap'
-- @
--
-- 'Swap' isn't a subclass of 'Bifunctor', as for example
--
-- >>> newtype Bipredicate a b = Bipredicate (a -> b -> Bool)
--
-- is not a 'Bifunctor' but has 'Swap' instance
--
-- >>> instance Swap Bipredicate where swap (Bipredicate p) = Bipredicate (flip p)
--
class Swap p where
    swap :: p a b -> p b a

instance Swap (,) where
    swap = Data.Tuple.swap

instance Swap Either where
    swap (Left x) = Right x
    swap (Right x) = Left x

instance Swap p => Swap (Flip p) where
    swap = Flip . swap . runFlip

instance (Swap p, Swap q) => Swap (Product p q) where
    swap (Pair p q) = Pair (swap p) (swap q)

instance (Swap p, Swap q) => Swap (Sum p q) where
    swap (L2 p) = L2 (swap p)
    swap (R2 q) = R2 (swap q)

instance (Functor f, Swap p) => Swap (Tannen f p) where
    swap = Tannen . fmap swap . runTannen

instance (f ~ g, Functor f, Swap p) => Swap (Biff p f g) where
    swap = Biff . swap . runBiff

instance Swap Validation where
    swap (Failure e) = Success e
    swap (Success a) = Failure a

-- | "Semigroup-y" 'Bifunctor's.
--
-- @
-- 'assoc' . 'unassoc' = 'id'
-- 'unassoc' . 'assoc' = 'id'
-- 'assoc' . 'bimap' ('bimap' f g) h = 'bimap' f ('bimap' g h) . 'assoc'
-- @
--
-- This library doesn't provide @Monoidal@ class, with left and right unitors.
-- Are they useful in practice?
--
class Assoc p where
    assoc :: p (p a b) c -> p a (p b c)
    unassoc :: p a (p b c) -> p (p a b) c

instance Assoc (,) where
    assoc ((a, b), c) = (a, (b, c))
    unassoc (a, (b, c)) = ((a, b), c)

instance Assoc Either where
    assoc (Left (Left a))  = Left a
    assoc (Left (Right b)) = Right (Left b)
    assoc (Right c)        = Right (Right c)

    unassoc (Left a)          = Left (Left a)
    unassoc (Right (Left b))  = Left (Right b)
    unassoc (Right (Right c)) = Right c

instance (Assoc p, Bifunctor p) => Assoc (Flip p) where
    assoc   = Flip . first Flip . unassoc . second runFlip . runFlip
    unassoc = Flip . second Flip . assoc . first runFlip . runFlip

-- $setup
--
-- TODO: make proper test-suite
--
-- >>> import Data.Proxy
-- >>> import Test.QuickCheck
-- >>> import Data.Functor.Classes
--
-- >>> :{
--     let assocUnassocLaw :: (Assoc p, Eq2 p) => Proxy p -> p Bool (p Int Char) -> Bool
--         assocUnassocLaw _ x = liftEq2 (==) eq2 (assoc (unassoc x)) x
--     :}
--
-- >>> quickCheck $ assocUnassocLaw (Proxy :: Proxy (,))
-- +++ OK, passed 100 tests.
--
-- >>> quickCheck $ assocUnassocLaw (Proxy :: Proxy Either)
-- +++ OK, passed 100 tests.
--
-- >>> :{
--     let unassocAssocLaw :: (Assoc p, Eq2 p) => Proxy p -> p (p Int Char) Bool -> Bool
--         unassocAssocLaw _ x = liftEq2 eq2 (==) (unassoc (assoc x)) x
--     :}
--
-- >>> quickCheck $ unassocAssocLaw (Proxy :: Proxy (,))
-- +++ OK, passed 100 tests.
--
-- >>> quickCheck $ unassocAssocLaw (Proxy :: Proxy Either)
-- +++ OK, passed 100 tests.
--
-- >>> :{
--     let bimapLaw :: (Assoc p, Eq2 p) => Proxy p
--                  -> Fun Int Char -> Fun Char Bool -> Fun Bool Int
--                  -> p (p Int Char) Bool
--                  -> Bool
--         bimapLaw _ (Fun _ f) (Fun _ g) (Fun _ h) x = liftEq2 (==) eq2
--             (assoc . bimap (bimap f g) h $ x)
--             (bimap f (bimap g h) . assoc $ x)
--     :}
--
-- >>> quickCheck $ bimapLaw (Proxy :: Proxy (,))
-- +++ OK, passed 100 tests.
--
-- >>> quickCheck $ bimapLaw (Proxy :: Proxy Either)
-- +++ OK, passed 100 tests.



class (Functor f, Contravariant f) => Phantom f where
  coerce :: f a -> f b
  coerce = phantom

instance Phantom (Const a)


class Profunctor p => InPhantom p where
  icoerce :: p a c -> p b c

instance (Bifunctor p, Profunctor p) => InPhantom p where
  icoerce = retagged

class Profunctor p => OutPhantom p where
  ocoerce :: p c a -> p c b

instance Phantom f => OutPhantom (Star f) where
  ocoerce (Star h) = Star $ coerce . h

instance OutPhantom (Forget f) where
  ocoerce (Forget f) = (Forget f)

-- Upstream imposes the 'Traversable' requirement.
instance (Phantom f, Traversable f) => InPhantom (Costar f) where
  icoerce (Costar h) = Costar $ h . coerce


-- Entailment relationships not already given by 'profunctors':
--class Equalizing (p :: * -> * -> *)
--instance Equalizing p

class (Strong p, Choice p) => AffineTraversing p
instance (Strong p, Choice p) => AffineTraversing p

class (InPhantom p, Choice p) => Reviewing p
instance (InPhantom p, Choice p) => Reviewing p

--class (Bifunctor p, Choice p) => Reviewing p
--instance (Bifunctor p, Choice p) => Reviewing p


class (OutPhantom p, Strong p) => Getting p
instance (OutPhantom p, Strong p) => Getting p


--class (Bicontravariant p, Strong p) => Getting p
--instance (Bicontravariant p, Strong p) => Getting p

--class (OutPhantom p, Traversing p) => Folding p

class (OutPhantom p, Traversing p) => Folding p
instance (OutPhantom p, Traversing p) => Folding p

class (OutPhantom p, Choice p, Traversing p) => AffineFolding p
instance (OutPhantom p, Choice p, Traversing p) => AffineFolding p


class Traversing1 p where
  traverse1' :: Traversable1 f => p a b -> p (f a) (f b)
  wander1 :: (forall f. Apply f => (a -> f b) -> s -> f t) -> p a b -> p s t

instance Apply f => Traversing1 (Star f) where
  traverse1' (Star f) = Star (traverse1 f)
  wander1 f (Star afb) = Star (f afb)

class (OutPhantom p, Traversing1 p) => Folding1 p
instance (OutPhantom p, Traversing1 p) => Folding1 p

{-



newtype ProIn p f a b = ProIn { proIn :: p (f a) b }

instance (Profunctor p, Functor f) => Profunctor (ProIn p f) where
  dimap f g (ProIn pab) = ProIn $ dimap (fmap f) g pab

instance (Profunctor p, Phantom f) => Choice (ProIn p f) where
  right' = _RightDefault

_RightDefault :: InPhantom p => p a b -> p (Either c a) (Either c b)
_RightDefault = icoerce . omap Right

instance (Profunctor p, Phantom f) => InPhantom (ProIn p f) where
  icoerce (ProIn pab) = ProIn $ imap coerce pab

newtype ProOut p g a b = ProOut { proOut :: p a (g b) }

instance (Profunctor p, Functor f) => Profunctor (ProOut p f) where
  dimap f g (ProOut pab) = ProOut $ dimap f (fmap g) pab

instance (Profunctor p, Phantom f) => Strong (ProOut p f) where
  second' = _2Default

_2Default :: OutPhantom p => p a b -> p (c, a) (c, b)
_2Default = ocoerce . imap snd

instance (Profunctor p, Phantom f) => OutPhantom (ProOut p f) where
  ocoerce (ProOut pab) = ProOut $ omap coerce pab
-}

module Data.Semiring.Endomorphism where
{-
(
  -- * 'End'
    lift
  , lower
  -- * Properties
  , prop_monomorphism_monoid 
  , prop_monomorphism_semiring
  -- * 'EndoT'
  , EndoT(..)
  , lift1
  , lower1
  --, anyOf
  -- * 'Exp'
  , Exp(..)
  , curry'
  , uncurry'
) where
-}

import Control.Applicative
import Control.Arrow ((***))
import Control.Monad
import Data.Semiring
import Data.Dioid
import Data.Bifunctor.Swap
import Data.Bifunctor.Assoc

import Data.Functor.Identity
import Data.List.NonEmpty (NonEmpty)

--import Data.Functor.Apply

import Lens.Micro (ASetter', (%~), over, sets)

import P

-- Boehm-Berarducci encoding @(a -> a) -> a -> a@ of an arbitrary semi-ring.
type Cayley a = ASetter' a a


-- >>> lower . endo $ fmap lift [1 .. (4::Int)]
-- 24
lift :: (Monoid a, Semiring a) => a -> Cayley a
lift a = sets $ \ f y -> a >< f zero <> y

infixl 6 %

(%) :: (Monoid a, Semiring a) => Cayley a -> Cayley a -> Cayley a
(%) = add

infix 4 <%

(<%) = (Monoid a, Dioid a) :: Cayley a -> Cayley a -> Bool
f <% g = lower f `ord` lower g

-- >>> lower $ lift 3 . lift 3 % lift 4 . lift 4 :: Int
-- 25
add :: (Monoid a, Semiring a) => Cayley a -> Cayley a -> Cayley a
add f g = sets $ \h -> (f %~ h) . (g %~ h)

lower :: (Monoid a, Semiring a) => Cayley a -> a
lower a = over a (one <>) zero

-- >>> lower $ zero' % one' :: Int
-- 1
-- >>> lower $ zero' . one' :: Int
-- 0
zero' :: (Monoid a, Semiring a) => Cayley a
zero' = sets $ const id

one' :: (Monoid a, Semiring a) => Cayley a
one' = sets id

sum :: (Foldable t, Monoid r, Semiring r) => t r -> r
sum = sumWith id

sumWith :: (Foldable t, Monoid r, Semiring r) => (a -> r) -> t a -> r
sumWith f = lower . foldr ((+) . lift . f) zero'

product :: (Foldable t, Monoid r, Semiring r) => t r -> r
product = productWith id

productWith :: (Foldable t, Monoid r, Semiring r) => (a -> r) -> t a -> r
productWith f = lower . foldr ((.) . lift . f) one'




{-

--prop_homomorphism_semigroup :: (Eq a, Semigroup a) => a -> a -> Bool

prop_homomorphism_monoid :: (Eq a, Monoid a) => End a -> Bool
prop_homomorphism_monoid (End f) = f mempty == mempty

-- | If @a@ is a monoid, then the map @a -> 'End' a@ is a monoid embedding.
prop_monomorphism_monoid :: (Eq a, Monoid a) => [a] -> Bool
prop_monomorphism_monoid = liftA2 (==) f g
  where f = lower . foldMap lift
        g = foldMap id

-- | If @a@ is a semiring, then the map @a -> 'Cayley' a@ is a semiring embedding.
prop_monomorphism_semiring :: (Eq a, Monoid a, Semiring a) => [NonEmpty a] -> Bool
prop_monomorphism_semiring = liftA2 (==) f g
  where f = lower' . (foldMap . foldMap1') lift'
        g = foldMap . foldMap1' $ id

prop_monomorphism_unital :: (Eq a, Monoid a, Semiring a) => [[a]] -> Bool
prop_monomorphism_unital = liftA2 (==) f g
  where f = lower' . (foldMap . foldMap') lift'
        g = foldMap . foldMap' $ id

-}

-- | Represents the closure of Day convolution over 'Exp'.
newtype EndoT f x = EndoT { appEndoT :: forall y. Exp f f y -> Exp f f (x, y) }

instance Functor f => Functor (EndoT f) where

  fmap f (EndoT z) = EndoT $ \fx -> fmap (\(x , y) -> (f x, y)) (z fx)


instance Functor f => Applicative (EndoT f) where

  pure v = EndoT $ \f -> fmap (\y -> (v, y)) f

  EndoT h <*> EndoT v = fmap (uncurry ($)) $ EndoT $ \f -> fmap ((swap *** id) . unassoc) (v (h f))

instance Functor f => Alternative (EndoT f) where

  empty = EndoT $ const (Exp $ \h x -> x)

  EndoT f <|> EndoT g = EndoT $ \h -> Exp (\j i -> runExp (f h) j (runExp (g h) j i))

lift1 :: Alternative f => f a -> EndoT f a
lift1 x = EndoT $ \g -> Exp (\f fx -> runExp g (flip (curry f)) empty <*> x <|> fx )

lower1 :: Alternative f => EndoT f a -> f a
lower1 (EndoT f) = runExp (f (Exp (\g i -> pure (g ()) <|> i))) fst empty

{-
-- | Fast alternative. We run first on 'EndoT []', and then flatten back the result to lists.
anyOf :: Alternative f => [a] -> f a
anyOf = lower1 . _anyOf

_anyOf :: Alternative f => [a] -> f a
_anyOf [ ] = empty
_anyOf (x : xs) = _anyOf xs <|> pure x

-}

-- | Exponential of the Cartesian product in the category of endofunctors.
newtype Exp f g x = Exp { runExp :: forall y. (x -> y) -> f y -> g y }

instance Functor (Exp f g) where fmap f c = Exp $ \xy -> runExp c (xy . f)


curry' :: (Functor f, Functor g, Functor h) => (forall x . (f x , g x ) -> h x ) -> (forall x . f x -> Exp g h x )
curry' f = \fx -> Exp (\t -> \gy -> f (fmap t fx , gy))

uncurry' :: (Functor f, Functor g, Functor h) => (forall x . f x -> Exp g h x) -> (forall x . (f x , g x ) -> h x)
uncurry' f = \fgx -> runExp (f (fst fgx)) id (snd fgx)


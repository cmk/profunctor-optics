module Data.Semiring.Endomorphism (
    endo
  , endoM
  -- * 'End'
  , End(..)
  , prod
  , lift
  , lift'
  , lower
  , lower'
  -- * Properties
  , prop_monomorphism_monoid 
  , prop_monomorphism_semiring
  -- * 'EndT'
  , EndT(..)
  , lift1
  , lower1
  --, anyOf
  -- * 'Exp'
  , Exp(..)
  , curry'
  , uncurry'
) where


import Control.Applicative
import Control.Arrow ((***))
--import Control.Category.Associative (disassociate)
--import Control.Category.Braided (swap)
import Control.Monad
import Data.Semiring
import Data.Dioid
import Data.Bifunctor.Swap
import Data.Bifunctor.Assoc

import Data.List.NonEmpty (NonEmpty)
{-# RULES
    "endo" forall f g.   endo [f, g]    = f . g;
    "endo" forall f g h. endo [f, g, h] = f . g . h;
    "endo" forall f fs.  endo (f:fs)    = f . endo fs
  #-}

endo :: Foldable t => t (a -> a) -> a -> a
endo = foldr (.) id

{-# INLINE [1] endo #-}

endoM :: (Monad m, Foldable t, Applicative m) => t (a -> m a) -> a -> m a
endoM = foldr (<=<) pure

{-# INLINE [1] endoM #-}

{-# RULES
    "endoM" forall f g.   endoM [f, g]    = f <=< g;
    "endoM" forall f g h. endoM [f, g, h] = f <=< g <=< h;
    "endoM" forall f fs.  endoM (f:fs)    = f <=< endoM fs
  #-}

{- |
Note that the property of right distributivity follows from the defining property of semigroup endomorphisms:

@appEnd ((f <> g) >< h) a ≡ appEnd h $ appEnd f a <> appEnd g a ≡ appEnd (h >< f) a <> appEnd (h >< g) a ≡ appEnd (f >< h <> g >< h) a@

Also note that the full monoid endomorphism property is required, otherwise the element 'h >< zero' is not absorbing for '><'.

Indeed, although we have 'prop_left_absorbative_zero':

@ forall h. End h >< zero ≡ zero @

but we do not necessarily have the (required) 'prop_right_absorbative_zero' for a full semiring:

@ forall h. zero >< End h ≡ zero @

unless  @h . const mempty ≡ const $ h mempty@

which has no reason to be true unless 'h' is a full moniod endomorphism.

-}

-- | The semiring of endomorphisms of a monoid under composition.
--
-- >>> let computation = End ("Hello, " ++) >< End (++ "!")
-- >>> appEnd computation "Haskell"
-- "Hello, Haskell!"

-- If 'a' is a commutative monoid, the set 'End a' of endomorphisms forms a semiring, where addition is pointwise addition and multiplication is function composition. 
-- The zero morphism and the identity are the respective neutral elements. 

-- This is a very useful construct. For instance, the type @forall a. 'End' ('End' a)@ is a valid encoding of Church numerals, with addition and multiplication being their semiring variants.

-- If @a@ is the additive monoid of natural numbers we obtain the semiring of natural numbers as 'End a'.
-- If @a@ is a finite semiring over n values, we obtain (after associating each morphism to a matrix) the semiring of square n-by-n matrices with coefficients in @a@.

newtype End a = End { appEnd :: a -> a } -- deriving Generic

-- Note that @a@ must be commutative for this instance to be legal?
instance Semigroup a => Semigroup (End a) where 

  End f <> End g = End $ liftA2 (<>) f g 


instance Monoid a => Monoid (End a) where 
  
  mempty = End (const mempty)


instance Monoid a => Semiring (End a) where 

  End f >< End g = End $ f . g
  {-# INLINE (><) #-}

  fromBoolean = fromBooleanDef $ End id


instance (Monoid a, Dioid a) => Dioid (End a) where

  f `ord` g = lower f `ord` lower g

--prop_homomorphism_semigroup :: (Eq a, Semigroup a) => a -> a -> Bool

prop_homomorphism_monoid :: (Eq a, Monoid a) => End a -> Bool
prop_homomorphism_monoid (End f) = f mempty == mempty

-- | If @a@ is a monoid, then the map @a -> 'End' a@ is a monoid embedding.
prop_monomorphism_monoid :: (Eq a, Monoid a) => [a] -> Bool
prop_monomorphism_monoid = liftA2 (==) f g
  where f = lower . foldMap lift
        g = foldMap id

-- | If @a@ is a semiring, then the map @a -> 'End' ('End' a)@ is a semiring embedding.
prop_monomorphism_semiring :: (Eq a, Monoid a, Semiring a) => [NonEmpty a] -> Bool
prop_monomorphism_semiring = liftA2 (==) f g
  where f = lower' . (foldMap . foldMap1') lift'
        g = foldMap . foldMap1' $ id

prop_monomorphism_unital :: (Eq a, Monoid a, Semiring a) => [[a]] -> Bool
prop_monomorphism_unital = liftA2 (==) f g
  where f = lower' . (foldMap . foldMap') lift'
        g = foldMap . foldMap' $ id

lift :: (Monoid a) => a -> End a
lift a = End (a <>)

lift' :: (Monoid a, Semiring a) => a -> End (End a)
lift' = liftProd . lift

lower :: (Monoid a) => End a -> a
lower (End f) = f mempty

lower' :: (Monoid a, Semiring a) => End (End a) -> a
lower' = lower . lowerProd

-- We can use the isomorphism between @End (End a)@ and @End a@ in order to reuse the multiplicative structure of @a@.
prod :: (Monoid a, Semiring a) => End a -> End a -> End a
prod f g = lift $ lower f >< lower g

liftProd :: (Monoid a, Semiring a) => End a -> End (End a)
liftProd a = End (a `prod`)

lowerProd :: (Monoid a, Semiring a) => End (End a) -> End a
lowerProd (End f) = f $ lift one

{-
foldrOf :: (Foldable t, Monoid c) => (a -> c -> c) -> c -> t a -> c
foldrOf f r = (`appEnd` r) . foldMap (End . f)

foldlOf' f c0 s = foldrOf (foo f) (End id) s 
-}


{-
lift'' a = (lift' a `mul'`)
mul' f g = lift' $ lower' f >< lower' g

liftProd' a = End (a `mul'`)

--liftAdd :: (Monoid a, Semiring a) => End a -> End (End a)
--liftAdd a = End $ const a
-}

-- | Represents the closure of Day convolution over 'Exp'.
newtype EndT f x = EndT { appEndT :: forall y. Exp f f y -> Exp f f (x, y) }

instance Functor f => Functor (EndT f) where

  fmap f (EndT z) = EndT $ \fx -> fmap (\(x , y) -> (f x, y)) (z fx)


instance Functor f => Applicative (EndT f) where

  pure v = EndT $ \f -> fmap (\y -> (v, y)) f

  EndT h <*> EndT v = fmap (uncurry ($)) $ EndT $ \f -> fmap ((swap *** id) . unassoc) (v (h f))

instance Functor f => Alternative (EndT f) where

  empty = EndT $ const (Exp $ \h x -> x)

  EndT f <|> EndT g = EndT $ \h -> Exp (\j i -> runExp (f h) j (runExp (g h) j i))

lift1 :: Alternative f => f a -> EndT f a
lift1 x = EndT $ \g -> Exp (\f fx -> runExp g (flip (curry f)) empty <*> x <|> fx )

lower1 :: Alternative f => EndT f a -> f a
lower1 (EndT f) = runExp (f (Exp (\g i -> pure (g ()) <|> i))) fst empty

{-
-- | Fast alternative. We run first on 'EndT []', and then flatten back the result to lists.
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


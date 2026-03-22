{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Prism (
    -- * Prism
    Prism
  , Prism'
  , prism
  , prism'
  , handling
  , clonePrism
    -- * Reprism
  , Reprism
  , Reprism'
  , reprism
  , reprism'
  , rehandling
  , cloneReprism
    -- * Optics
  , left
  , right
  , releft
  , reright
  , just
  , nothing
  , prefixed
  , only
  , nearly
  , nthbit
    -- * Operators
  , aside
  , without
  , below
  , toPastroSum
  , toTambaraSum
  , withPrism
  , withReprism
    -- * Classes
  , Choice(..)
  , Cochoice(..)
) where

import Control.Monad (guard)
import Data.Bifunctor as B
import Data.Bits (Bits, bit, testBit)
import Data.List (stripPrefix,(++))
import Data.Profunctor.Choice
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Import 
import Data.Profunctor.Optic.Types
-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> :set -XTypeOperators
-- >>> :set -XRankNTypes
-- >>> import Data.Function ((&))
-- >>> import Data.List.NonEmpty
-- >>> :load Data.Profunctor.Optic
-- >>> import Prelude

---------------------------------------------------------------------
-- 'Prism' & 'Cxprism'
---------------------------------------------------------------------

-- | Obtain a 'Prism' from a constructor and a matcher function.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input functions satisfy the following
-- properties:
--
-- * @sta (bt b) ≡ Right b@
--
-- * @(either id bt) (sta s) ≡ s@
--
-- * @left sta (sta s) ≡ left Left (sta s)@
--
-- More generally, a profunctor optic must be monoidal as a natural 
-- transformation:
-- 
-- * @o id ≡ id@
--
-- * @o ('Data.Profunctor.Composition.Procompose' p q) ≡ 'Data.Profunctor.Composition.Procompose' (o p) (o q)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
prism :: (s -> t + a) -> (b -> t) -> Prism s t a b
prism sta bt pab = dimap sta (either id bt) (right' pab)

-- | Obtain a 'Prism'' from a reviewer and a matcher function that produces a 'Maybe'.
--
-- /Note/: The arguments are reversed from the equivalent in the /lens/ package.
-- This is unfortunate but done to maintain cosistency with 'traversal0' etc.
--
prism' :: (s -> Maybe a) -> (b -> s) -> Prism s s a b
prism' sa as = prism (\s -> maybe (Left s) Right (sa s)) as

-- | Obtain a 'Prism' from its free tensor representation.
--
-- Useful for constructing prisms from try and handle functions.
--
handling :: (s -> c + a) -> (c + b -> t) -> Prism s t a b
handling sca cbt pab = dimap sca cbt (right' pab)

-- | TODO: Document
--
clonePrism :: APrism s t a b -> Prism s t a b
clonePrism o = withPrism o $ \sta bt -> prism sta bt

---------------------------------------------------------------------
-- 'Reprism'
---------------------------------------------------------------------

-- | Obtain a 'Reprism' from a viewer and a matcher.
--
-- @'reprism' sa bat ≡ 're' ('prism' sta bt)@ (with roles swapped)
--
-- A 'Reprism' is simultaneously a 'View' and a 'Review':
--
-- @
-- 'Data.Profunctor.Optic.View.view' ('reprism' sa bat) ≡ sa
-- @
--
reprism :: (s -> a) -> (b -> Either a t) -> Reprism s t a b
reprism sa bat = unright . dimap (either id sa) bat
{-# INLINE reprism #-}

-- | Obtain a simple 'Reprism' from a viewer and a 'Maybe' matcher.
--
reprism' :: (s -> a) -> (a -> Maybe s) -> Reprism' s a
reprism' sa as = reprism sa $ \b -> maybe (Left b) Right (as b)
{-# INLINE reprism' #-}

-- | Obtain a 'Reprism' from its free tensor representation.
--
rehandling :: (Either c s -> a) -> (b -> Either c t) -> Reprism s t a b
rehandling csa bct = unright . dimap csa bct
{-# INLINE rehandling #-}

-- | Clone a 'Reprism'.
--
cloneReprism :: AReprism s t a b -> Reprism s t a b
cloneReprism o = withReprism o reprism
{-# INLINE cloneReprism #-}

---------------------------------------------------------------------
-- Common 'Prism's and 'Coprism's
---------------------------------------------------------------------

-- | Focus on the `Left` constructor of `Either`.
--
left :: Prism (a + c) (b + c) a b
left pab = left' pab

-- | Focus on the `Right` constructor of `Either`.
--
right :: Prism (c + a) (c + b) a b
right pab = right' pab

-- | 'Reprism' out of the @Left@ constructor.
--
-- @'releft' ≡ 're' 'left'@
--
releft :: Reprism a b (Either a c) (Either b c)
releft = unleft
{-# INLINE releft #-}

-- | 'Reprism' out of the @Right@ constructor.
--
-- @'reright' ≡ 're' 'right'@
--
reright :: Reprism a b (Either c a) (Either c b)
reright = unright
{-# INLINE reright #-}

-- | Focus on the `Just` constructor of `Maybe`.
--
-- >>> Just 1 :| [Just 2, Just 3] & cotraverseOf just sum
-- Just 6
-- >>> Nothing :| [Just 2, Just 3] & cotraverseOf just sum
-- Nothing
--
just :: Prism (Maybe a) (Maybe b) a b
just = prism (maybe (Left Nothing) Right) Just

-- | Focus on the `Nothing` constructor of `Maybe`.
--
nothing :: Prism (Maybe a) (Maybe b) () ()
nothing = prism (maybe (Right ()) (const $ Left Nothing)) (const Nothing)

-- | Focus on the remainder of a list with a given prefix.
--
prefixed :: Eq a => [a] -> Prism' [a] [a]
prefixed ps = prism' (stripPrefix ps) (ps ++)

-- | Focus not just on a case, but a specific value of that case.
--
only :: Eq a => a -> Prism' a ()
only x = nearly x (x==)

-- | Create a 'Prism' from a value and a predicate.
--
-- >>> review (nearly [] null) ()
-- []
-- >>> [1,2,3,4] ^? nearly [] null
-- Nothing
--
-- @'nearly' [] 'Prelude.null' :: 'Prism'' [a] ()@
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that @f x@ holds iff @x ≡ a@. 
--
nearly :: a -> (a -> Bool) -> Prism' a ()
nearly x f = prism' (guard . f) (const x)

-- | Focus on the truth value of the nth bit in a bit array.
--
nthbit :: Bits s => Int -> Prism' s ()
nthbit n = prism' (guard . (flip testBit n)) (const $ bit n)

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Use a 'Prism' to lift part of a structure.
--
aside :: APrism s t a b -> Prism (e , s) (e , t) (e , a) (e , b)
aside k =
  withPrism k $ \sta bt ->
    prism (\(e,s) -> case sta s of
             Left t  -> Left  (e,t)
             Right a -> Right (e,a))
          (fmap bt)
{-# INLINE aside #-}

-- | Given a pair of prisms, project sums.
without :: APrism s t a b -> APrism u v c d -> Prism (s + u) (t + v) (a + c) (b + d)
without k =
  withPrism k $ \sta bt k' ->
    withPrism k' $ \uevc dv ->
      prism (\su -> case su of
               Left s  -> bimap Left Left (sta s)
               Right u -> bimap Right Right (uevc u))
            (bimap bt dv)
{-# INLINE without #-}

-- | Lift a 'Prism' through a 'Traversable' functor.
-- 
-- Returns a 'Prism' that matchOf only if each element matchOf the original 'Prism'.
--
-- >>> [Left 1, Right "foo", Left 4, Right "woot"] ^.. below right'
-- []
-- >>> [Right "hail hydra!", Right "foo", Right "blah", Right "woot"] ^.. below right'
-- [["hail hydra!","foo","blah","woot"]]
--
below :: Traversable f => APrism' s a -> Prism' (f s) (f a)
below k =
  withPrism k $ \sta bt ->
    prism (\s -> case traverse sta s of
             Left _  -> Left s
             Right t -> Right t)
          (fmap bt)
{-# INLINE below #-}

-- | Use a 'Prism' to construct a 'PastroSum'.
--
toPastroSum :: APrism s t a b -> p a b -> PastroSum p s t
toPastroSum o p = withPrism o $ \sta bt -> PastroSum (join . B.first bt) p (eswap . sta)

-- | Use a 'Prism' to construct a 'TambaraSum'.
--
toTambaraSum :: Choice p => APrism s t a b -> p a b -> TambaraSum p s t
toTambaraSum o p = withPrism o $ \sta bt -> TambaraSum (left' . prism sta bt $ p)

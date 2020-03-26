{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Prism (
    -- * Prism & Cxprism
    Prism
  , Prism'
  , Coprism
  , Coprism'
  , prism
  , prism'
  , handling
  , clonePrism
  , coprism
  , coprism'
  , rehandling
  , cloneCoprism
    -- * Optics
  , left
  , right
  , coleft
  , coright
  , just
  , cojust
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
  , withCoprism
    -- * Classes
  , Choice(..)
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
-- * @(id ||| bt) (sta s) ≡ s@
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
prism sta bt = dimap sta (id ||| bt) . right'

-- | Obtain a 'Prism'' from a reviewer and a matcher function that produces a 'Maybe'.
--
-- /Note/: The arguments are reversed from the equivalent in the /lens/ package.
-- This is unfortunate but done to maintain cosistency with 'traversal0' etc.
--
prism' :: (s -> Maybe a) -> (b -> s) -> Prism s s a b
prism' sa as = flip prism as $ \s -> maybe (Left s) Right (sa s)

-- | Obtain a 'Prism' from its free tensor representation.
--
-- Useful for constructing prisms from try and handle functions.
--
handling :: (s -> c + a) -> (c + b -> t) -> Prism s t a b
handling sca cbt = dimap sca cbt . right'

-- | TODO: Document
--
clonePrism :: APrism s t a b -> Prism s t a b
clonePrism o = withPrism o prism

-- | Obtain a 'Cochoice' optic from a constructor and a matcher function.
--
-- @
-- coprism f g ≡ \f g -> re (prism f g)
-- @
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input functions satisfy the following
-- properties:
--
-- * @bat (bt b) ≡ Right b@
--
-- * @(id ||| bt) (bat b) ≡ b@
--
-- * @left bat (bat b) ≡ left Left (bat b)@
--
-- A 'Coprism' is a 'View', so you can specialise types to obtain:
--
-- @ view :: 'Coprism'' s a -> s -> a @
--
coprism :: (s -> a) -> (b -> a + t) -> Coprism s t a b
coprism sa bat = unright . dimap (id ||| sa) bat

-- | Create a 'Coprism' from a reviewer and a matcher function that produces a 'Maybe'.
--
coprism' :: (s -> a) -> (a -> Maybe s) -> Coprism' s a
coprism' tb bt = coprism tb $ \b -> maybe (Left b) Right (bt b)

-- | Obtain a 'Coprism' from its free tensor representation.
--
rehandling :: (c + s -> a) -> (b -> c + t) -> Coprism s t a b
rehandling csa bct = unright . dimap csa bct

-- | TODO: Document
--
cloneCoprism :: ACoprism s t a b -> Coprism s t a b
cloneCoprism o = withCoprism o coprism

---------------------------------------------------------------------
-- Common 'Prism's and 'Coprism's
---------------------------------------------------------------------

-- | Focus on the `Left` constructor of `Either`.
--
left :: Prism (a + c) (b + c) a b
left = left'

-- | Focus on the `Right` constructor of `Either`.
--
right :: Prism (c + a) (c + b) a b
right = right'

-- | Co-focus on the `Left` constructor of `Either`.
--
coleft :: Coprism a b (a + c) (b + c)
coleft = unleft

-- | Co-focus on the `Right` constructor of `Either`.
--
coright :: Coprism a b (c + a) (c + b)
coright = unright

-- | Focus on the `Just` constructor of `Maybe`.
--
-- >>> Just 1 :| [Just 2, Just 3] & cotraverses just sum
-- Just 6
-- >>> Nothing :| [Just 2, Just 3] & cotraverses just sum
-- Nothing
--
just :: Prism (Maybe a) (Maybe b) a b
just = flip prism Just $ maybe (Left Nothing) Right

-- | Co-focus on the `Just` constructor of `Maybe`.
--
cojust :: Coprism a b (Maybe a) (Maybe b)
cojust = coprism Just $ maybe (Left Nothing) Right

-- | Focus on the `Nothing` constructor of `Maybe`.
--
nothing :: Prism (Maybe a) (Maybe b) () ()
nothing = flip prism (const Nothing) $ maybe (Right ()) (const $ Left Nothing)

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
    flip prism (fmap bt) $ \(e,s) ->
      case sta s of
        Left t  -> Left  (e,t)
        Right a -> Right (e,a)
{-# INLINE aside #-}

-- | Given a pair of prisms, project sums.
without :: APrism s t a b -> APrism u v c d -> Prism (s + u) (t + v) (a + c) (b + d)
without k =
  withPrism k $ \sta bt k' ->
    withPrism k' $ \uevc dv ->
      flip prism (bimap bt dv) $ \su ->
        case su of
          Left s  -> bimap Left Left (sta s)
          Right u -> bimap Right Right (uevc u)
{-# INLINE without #-}

-- | Lift a 'Prism' through a 'Traversable' functor.
-- 
-- Returns a 'Prism' that matches only if each element matches the original 'Prism'.
--
-- >>> [Left 1, Right "foo", Left 4, Right "woot"] ^.. below right'
-- []
-- >>> [Right "hail hydra!", Right "foo", Right "blah", Right "woot"] ^.. below right'
-- [["hail hydra!","foo","blah","woot"]]
--
below :: Traversable f => APrism' s a -> Prism' (f s) (f a)
below k =
  withPrism k $ \sta bt ->
    flip prism (fmap bt) $ \s ->
      case traverse sta s of
        Left _  -> Left s
        Right t -> Right t
{-# INLINE below #-}

-- | Use a 'Prism' to construct a 'PastroSum'.
--
toPastroSum :: APrism s t a b -> p a b -> PastroSum p s t
toPastroSum o p = withPrism o $ \sta bt -> PastroSum (join . B.first bt) p (eswap . sta)

-- | Use a 'Prism' to construct a 'TambaraSum'.
--
toTambaraSum :: Choice p => APrism s t a b -> p a b -> TambaraSum p s t
toTambaraSum o p = withPrism o $ \sta bt -> TambaraSum (left' . prism sta bt $ p)

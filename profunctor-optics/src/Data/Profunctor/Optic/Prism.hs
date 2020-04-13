{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE PackageImports        #-}
module Data.Profunctor.Optic.Prism (
    -- * Prism
    Prism
  , Prism'
  , prism
  , prism'
  , handling
  , clonePrism
  , aside
  , without
  , below
  , toPastroSum
  , toTambaraSum
    -- * Optics
  , left
  , right
  , just
  , nothing
  , prefixed
  , only
  , nearly
  , nthbit
  , sync
  , async
  , exception
  , asynchronous
    -- * Classes
  , Choice(..)
) where

import Control.Exception as Ex
import Control.Monad (guard)
import Data.Bifunctor as B
import Data.Bits (Bits, bit, testBit)
import Data.List (stripPrefix,(++))
import Data.Profunctor.Choice
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Import 
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Combinator 
import GHC.IO.Exception (IOErrorType)
import qualified GHC.IO.Exception as Ghc

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

-- | Focus on the `Just` constructor of `Maybe`.
--
-- >>> Just 1 :| [Just 2, Just 3] & cotraverses just sum
-- Just 6
-- >>> Nothing :| [Just 2, Just 3] & cotraverses just sum
-- Nothing
--
just :: Prism (Maybe a) (Maybe b) a b
just = flip prism Just $ maybe (Left Nothing) Right

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

-- | Focus on whether an exception is synchronous.
--
sync :: Exception e => Prism' e e 
sync = filterOn $ \e -> case fromException (toException e) of
  Just (SomeAsyncException _) -> False
  Nothing -> True
  where filterOn f = dimap (branch' f) join . right'

-- | Focus on whether an exception is asynchronous.
--
async :: Exception e => Prism' e e 
async = filterOn $ \e -> case fromException (toException e) of
  Just (SomeAsyncException _) -> True
  Nothing -> False
  where filterOn f = dimap (branch' f) join . right'

-- | Focus on whether a given exception has occurred.
--
-- @
-- exception @IOException :: Prism' SomeException IOException
-- @
--
exception :: Exception e => Prism' SomeException e
exception = prism' fromException toException

-- | Focus on whether a given asynchronous exception has occurred.
--
asynchronous :: Exception e => Prism' SomeException e
asynchronous = prism' asyncExceptionFromException asyncExceptionToException

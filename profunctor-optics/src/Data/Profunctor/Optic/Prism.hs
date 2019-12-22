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
  , Cxprism
  , Cxprism'
  , prism
  , prism'
  , kprism
  , handling
  , clonePrism
    -- * Optics
  , kright
  , just
  , kjust
  , nothing
  , compared
  , prefixed
  , only
  , nearly
  , nthbit
  , sync
  , async
  , exception
  , asyncException
    -- * Primitive operators
  , withPrism
    -- * Operators
  , aside
  , without
  , below
  , toPastroSum
  , toTambaraSum
    -- * Classes
  , Choice(..)
) where

import Control.Exception
import Control.Monad (guard)
import Data.Bifunctor as B
import Data.Bits (Bits, bit, testBit)
import Data.List (stripPrefix)
import Data.Prd
import Data.Profunctor.Choice
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Iso
import Data.Profunctor.Optic.Import 
import Data.Profunctor.Optic.Types

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> :set -XTypeOperators
-- >>> :set -XRankNTypes
-- >>> import Data.Int.Instance ()
-- >>> import Data.List.NonEmpty
-- >>> :load Data.Profunctor.Optic
-- >>> let catchOn :: Int -> Cxprism' Int (Maybe String) String ; catchOn n = kjust $ \k -> if k==n then Just "caught" else Nothing
-- >>> let catchFoo :: b -> Cxprism String (String + a) (String + b) a b; catchFoo b = kright $ \e k -> if e == "fooError" && k == mempty then Right b else Left e

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
prism' :: (s -> Maybe a) -> (a -> s) -> Prism' s a
prism' sa as = flip prism as $ \s -> maybe (Left s) Right (sa s)

-- | Obtain a 'Cxprism'' from a reviewer and a matcher function that returns either a match or a failure handler.
--
kprism :: (s -> (k -> t) + a) -> (b -> t) -> Cxprism k s t a b
kprism skta bt = prism skta (bt .)

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

---------------------------------------------------------------------
-- Common 'Prism's and 'Coprism's
---------------------------------------------------------------------

-- | Focus on the `Just` constructor of `Maybe`.
--
-- >>> Just 1 :| [Just 2, Just 3] & just //~ sum
-- Just 6
--
-- >>> Nothing :| [Just 2, Just 3] & just //~ sum
-- Nothing
--
just :: Prism (Maybe a) (Maybe b) a b
just = flip prism Just $ maybe (Left Nothing) Right

-- | Focus on the `Nothing` constructor of `Maybe`.
--
nothing :: Prism (Maybe a) (Maybe b) () ()
nothing = flip prism (const Nothing) $ maybe (Right ()) (const $ Left Nothing)

-- | Focus on comparability to a given element of a partial order.
--
compared :: Eq a => Prd a => a -> Prism' a Ordering
compared x = flip prism' (const x) (pcompare x)

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
-- >>> nearly [] null #^ ()
-- []
--
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
  where filterOn f = iso (branch' f) join . right'

-- | Focus on whether an exception is asynchronous.
--
async :: Exception e => Prism' e e 
async = filterOn $ \e -> case fromException (toException e) of
  Just (SomeAsyncException _) -> True
  Nothing -> False
  where filterOn f = iso (branch' f) join . right'

-- | Focus on whether a given exception has occurred.
--
exception :: Exception e => Prism' SomeException e
exception = prism' fromException toException

-- | Focus on whether a given asynchronous exception has occurred.
--
asyncException :: Exception e => Prism' SomeException e
asyncException = prism' asyncExceptionFromException asyncExceptionToException

---------------------------------------------------------------------
-- Coindexed optics
---------------------------------------------------------------------

-- | Coindexed prism into the `Right` constructor of `Either`.
--
-- >>> kset (catchFoo "Caught foo") id $ Left "fooError"
-- Right "Caught foo"
--
-- >>> kset (catchFoo "Caught foo") id $ Left "barError"
-- Left "barError"
--
kright :: (e -> k -> e + b) -> Cxprism k (e + a) (e + b) a b
kright ekeb = flip kprism Right $ either (Left . ekeb) Right

-- | Coindexed prism into the `Just` constructor of `Maybe`.
--
-- >>> Just "foo" & catchOn 1 ##~ (\k msg -> show k ++ ": " ++ msg)
-- Just "0: foo"
--
-- >>> Nothing & catchOn 1 ##~ (\k msg -> show k ++ ": " ++ msg)
-- Nothing
--
-- >>> Nothing & catchOn 0 ##~ (\k msg -> show k ++ ": " ++ msg)
-- Just "caught"
--
kjust :: (k -> Maybe b) -> Cxprism k (Maybe a) (Maybe b) a b
kjust kb = flip kprism Just $ maybe (Left kb) Right

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
--
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

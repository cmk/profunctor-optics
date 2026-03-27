{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}

-- | Left and right carriers are characterized by their representation
-- functors ('Rep' and 'Corep'). 'Iso' sits at the top where both
-- are trivial ('Identity'). 'Adjoint' sits at the bottom where they
-- form a full adjunction (@'Corep' p ⊣ 'Rep' p@). A left-indexed
-- ('Ix') optic threads an index through the left adjoint functor
-- @(,) k@, while a right-indexed ('Cx') optic threads a coindex
-- through the right adjoint functor @(->) k@.
module Data.Profunctor.Optic.Prism (
    -- * Constructors
    -- ** Prism, Ixprism
    Prism, Prism'
  , Ixprism, Ixprism'
  , prism, prism'
  , ixprism, ixprism'
  , handling
  , ixhandling
  , clonePrism
  , cloneIxprism
    -- ** Reprism, Rxprism
  , Reprism, Reprism'
  , Rxprism, Rxprism'
  , reprism, reprism'
  , rxprism, rxprism'
  , rehandling
  , rehandling'
  , cloneReprism
    -- * Optics
    -- ** Prism, Ixprism
  , left, right
  , just, nothing
  , ixleft, ixright, ixjust
  , prefixed
  , only
  , nearly
  , nthbit
    -- ** Reprism, Rxprism
  , releft, reright
    -- * Operators
  , aside
  , without
  , below
  , withPrism
  , withIxprism
  , pastroSum
  , tambaraSum
    -- * Dual Operators
  , rematches
  , withReprism
    -- * Reexports
  , Choice(..)
  , Cochoice(..)
) where

import Data.Bifunctor as B
import Data.Bits (Bits, bit, testBit)
import Data.List (stripPrefix)
import Data.Profunctor.Choice hiding (tambaraSum, pastroSum)
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Arrow (eswap, join)
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
-- * Constructors
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
-- This is unfortunate but done to maintain consistency with 'traversal0' etc.
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

-- | Obtain an 'Ixprism' from an indexed matcher and a constructor.
--
-- @since 0.0.3
ixprism :: (s -> t + (k , a)) -> (b -> t) -> Ixprism k s t a b
ixprism stka bt = prism (\(_, s) -> stka s) bt
{-# INLINE ixprism #-}

-- | Obtain an 'Ixprism'' from an indexed matcher and a constructor.
--
-- @since 0.0.3
ixprism' :: (s -> Maybe (k , a)) -> (b -> s) -> Ixprism k s s a b
ixprism' ska bs = ixprism (\s -> maybe (Left s) Right (ska s)) bs
{-# INLINE ixprism' #-}

-- | Clone an 'Ixprism'.
--
-- @since 0.0.3
cloneIxprism :: Monoid k => AIxprism k s t a b -> Ixprism k s t a b
cloneIxprism o = withIxprism o ixprism
{-# INLINE cloneIxprism #-}

-- | Indexed 'handling': obtain an 'Ixprism' from an indexed matcher
-- and a constructor on the complement.
--
-- @since 0.0.3
ixhandling :: (s -> c + (k, a)) -> (c + b -> t) -> Ixprism k s t a b
ixhandling scka cbt = handling (\(_, s) -> scka s) cbt
{-# INLINE ixhandling #-}

---------------------------------------------------------------------
-- ** Reversed Constructors
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

-- | Obtain a 'Reprism' from a single discriminating function.
--
-- @
-- 'rehandling'' f ≡ 'rehandling' (either id id) f
-- @
--
rehandling' :: (b -> Either s t) -> Reprism s t s b
rehandling' f = unright . dimap (either id id) f
{-# INLINE rehandling' #-}

-- | Clone a 'Reprism'.
--
cloneReprism :: AReprism s t a b -> Reprism s t a b
cloneReprism o = withReprism o reprism
{-# INLINE cloneReprism #-}

-- | Indexed 'Reprism': coindexed by @k@.
--
-- The viewer returns @(k, a)@ and the matcher returns @(k, a) + t@.
--
-- @since 0.0.3
rxprism :: (s -> (k, a)) -> (b -> (k, a) + t) -> Rxprism k s t a b
rxprism ska bat = reprism (\(_, s) -> ska s) bat
{-# INLINE rxprism #-}

-- | Simple indexed 'Reprism' from a viewer and a 'Maybe' matcher.
--
-- @since 0.0.3
rxprism' :: Monoid k => (s -> (k, a)) -> ((k, a) -> Maybe s) -> Rxprism' k s a
rxprism' ska kas = rxprism ska $ \b -> maybe (Left (mempty, b)) Right (kas (mempty, b))
{-# INLINE rxprism' #-}

-- TODO: cloneRxprism needs ARxprism carrier type (deferred)

---------------------------------------------------------------------
-- * Optics
---------------------------------------------------------------------

-- | Focus on the `Left` constructor of `Either`.
--
left :: Prism (a + c) (b + c) a b
left pab = left' pab

-- | Focus on the `Right` constructor of `Either`.
--
right :: Prism (c + a) (c + b) a b
right pab = right' pab

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

-- | Indexed 'left'. The index is 'mempty'.
--
-- @since 0.0.3
ixleft :: Monoid k => Ixprism k (a + c) (b + c) a b
ixleft = ixprism (either (\a -> Right (mempty, a)) (Left . Right)) Left

-- | Indexed 'right'. The index is 'mempty'.
--
-- @since 0.0.3
ixright :: Monoid k => Ixprism k (c + a) (c + b) a b
ixright = ixprism (either (Left . Left) (\a -> Right (mempty, a))) Right

-- | Indexed 'just'. The index is 'mempty'.
--
-- @since 0.0.3
ixjust :: Monoid k => Ixprism k (Maybe a) (Maybe b) a b
ixjust = ixprism (maybe (Left Nothing) (\a -> Right (mempty, a))) Just

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
-- ** Reversed Optics
---------------------------------------------------------------------

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

---------------------------------------------------------------------
-- * Operators
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
pastroSum :: APrism s t a b -> p a b -> PastroSum p s t
pastroSum o p = withPrism o $ \sta bt -> PastroSum (join . B.first bt) p (eswap . sta)

-- | Use a 'Prism' to construct a 'TambaraSum'.
--
tambaraSum :: Choice p => APrism s t a b -> p a b -> TambaraSum p s t
tambaraSum o p = withPrism o $ \sta bt -> TambaraSum (left' . prism sta bt $ p)

---------------------------------------------------------------------
-- ** Reversed Operators
---------------------------------------------------------------------

-- | The Re-dual of 'Data.Profunctor.Optic.Traversal.matchOf': match
-- through a 'Reprism', going in the reverse direction.
--
-- @
-- 'matchOf'    :: 'APrism'   s t a b -> s -> t + a
-- 'rematches' :: 'AReprism' s t a b -> b -> a + t
-- @
--
-- 'rematches' accepts any optic with a 'ReprismRep' carrier
-- ('AReprism'), including 'Reprism', 'Iso', and any optic that is
-- both 'Choice' and 'Cochoice'.
--
-- /Example/: filter an Either-producing 'Sort' to the Left branch:
--
-- @
-- 'rematches' 'releft' :: b -> (Either a c) + a
-- @
--
rematches :: AReprism s t a b -> b -> a + t
rematches o b = withReprism o $ \_ bat -> bat b
{-# INLINE rematches #-}

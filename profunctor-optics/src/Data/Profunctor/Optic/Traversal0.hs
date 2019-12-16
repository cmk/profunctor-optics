{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Traversal0 (
    -- * Traversal0 & Ixtraversal0
    Traversal0
  , Traversal0'
  , Ixtraversal0
  , Ixtraversal0'
  , traversal0
  , traversal0'
  , itraversal0
  , itraversal0'
  , traversal0Vl
  , itraversal0Vl
    -- * Optics
  , nulled
  , selected
    -- * Primitive operators
  , withTraversal0
    -- * Operators
  , is
  , isnt
  , matches
    -- * Carriers
  , Traversal0Rep(..)
  , ATraversal0 
  , ATraversal0'
    -- * Classes
  , Strong(..)
  , Choice(..)
  , Costrong(..)
  , Cochoice(..)
) where

import Data.Bifunctor (first, second)
import Data.Profunctor.Optic.Lens
import Data.Profunctor.Optic.Prism
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Types

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XFlexibleContexts
-- >>> :set -XTypeApplications
-- >>> :set -XTupleSections
-- >>> :set -XRankNTypes
-- >>> import Data.Maybe
-- >>> import Data.List.NonEmpty (NonEmpty(..))
-- >>> import qualified Data.List.NonEmpty as NE
-- >>> import Data.Functor.Identity
-- >>> import Data.List.Index
-- >>> :load Data.Profunctor.Optic
-- >>> let catchOn :: Int -> Cxprism' Int (Maybe String) String ; catchOn n = kjust $ \k -> if k==n then Just "caught" else Nothing
-- >>> let itraversed :: Ixtraversal Int [a] [b] a b ; itraversed = itraversalVl itraverse

---------------------------------------------------------------------
-- 'Traversal0' & 'Ixtraversal0'
---------------------------------------------------------------------

-- | Create a 'Traversal0' from match and constructor functions.
--
-- /Caution/: In order for the 'Traversal0' to be well-defined,
-- you must ensure that the input functions satisfy the following
-- properties:
--
-- * @sta (sbt a s) ≡ either (Left . const a) Right (sta s)@
--
-- * @either id (sbt s) (sta s) ≡ s@
--
-- * @sbt (sbt s a1) a2 ≡ sbt s a2@
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
traversal0 :: (s -> t + a) -> (s -> b -> t) -> Traversal0 s t a b
traversal0 sta sbt = dimap (\s -> (s,) <$> sta s) (id ||| uncurry sbt) . right' . second'

-- | Obtain a 'Traversal0'' from match and constructor functions.
--
traversal0' :: (s -> Maybe a) -> (s -> a -> s) -> Traversal0' s a
traversal0' sa sas = flip traversal0 sas $ \s -> maybe (Left s) Right (sa s)

-- | TODO: Document
--
itraversal0 :: (s -> t + (i , a)) -> (s -> b -> t) -> Ixtraversal0 i s t a b
itraversal0 stia sbt = itraversal0Vl $ \point f s -> either point (fmap (sbt s) . uncurry f) (stia s)

-- | TODO: Document
--
itraversal0' :: (s -> Maybe (i , a)) -> (s -> a -> s) -> Ixtraversal0' i s a
itraversal0' sia = itraversal0 $ \s -> maybe (Left s) Right (sia s) 

-- | Transform a Van Laarhoven 'Traversal0' into a profunctor 'Traversal0'.
--
traversal0Vl :: (forall f. Functor f => (forall c. c -> f c) -> (a -> f b) -> s -> f t) -> Traversal0 s t a b
traversal0Vl f = dimap (\s -> (s,) <$> eswap (sat s)) (id ||| uncurry sbt) . right' . second'
  where
    sat = f Right Left
    sbt s b = runIdentity $ f Identity (\_ -> Identity b) s

-- | Transform an indexed Van Laarhoven 'Traversal0' into an indexed profunctor 'Traversal0'.
--
itraversal0Vl :: (forall f. Functor f => (forall c. c -> f c) -> (i -> a -> f b) -> s -> f t) -> Ixtraversal0 i s t a b
itraversal0Vl f = traversal0Vl $ \cc iab -> f cc (curry iab) . snd

-- | Create a 'Cotraversal0' from match and constructor functions.
--
-- /Caution/: In order for the 'Traversal0' to be well-defined,
-- you must ensure that the input functions satisfy the following
-- properties:
--
-- * @TODO@
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
cotraversal0 :: (s -> t + (k -> a)) -> ((k -> b) -> t) -> Cotraversal0 s t a b 
cotraversal0 stka kbt = prism stka kbt . closed

---------------------------------------------------------------------
-- Optics 
---------------------------------------------------------------------

-- | TODO: Document
--
nulled :: Traversal0' s a
nulled = traversal0 Left const 
{-# INLINE nulled #-}

-- | TODO: Document
--
selected :: (a -> Bool) -> Traversal0' (a, b) b
selected p = traversal0 (\kv@(k,v) -> branch p kv v k) (\kv@(k,_) v' -> if p k then (k,v') else kv)
{-# INLINE selected #-}

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | TODO: Document
--
withTraversal0 :: ATraversal0 s t a b -> ((s -> t + a) -> (s -> b -> t) -> r) -> r
withTraversal0 o k = case o (Traversal0Rep Right $ const id) of Traversal0Rep x y -> k x y

-- | TODO: Document
--
withCotraversal0 :: ACotraversal0 s t a b -> ((((s -> t + a) -> b) -> t) -> r) -> r
withCotraversal0 o k = case o (Cotraversal0Rep $ \f -> f Right) of Cotraversal0Rep g -> k g

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Check whether the optic is matched.
--
-- >>> is just Nothing
-- False
--
is :: ATraversal0 s t a b -> s -> Bool
is o = either (const False) (const True) . matches o
{-# INLINE is #-}

-- | Check whether the optic isn't matched.
--
-- >>> isnt just Nothing
-- True
--
isnt :: ATraversal0 s t a b -> s -> Bool
isnt o = either (const True) (const False) . matches o
{-# INLINE isnt #-}

-- | Test whether the optic matches or not.
--
-- >>> matches just (Just 2)
-- Right 2
--
-- >>> matches just (Nothing :: Maybe Int) :: Either (Maybe Bool) Int
-- Left Nothing
--
matches :: ATraversal0 s t a b -> s -> t + a
matches o = withTraversal0 o $ \sta _ -> sta
{-# INLINE matches #-}

---------------------------------------------------------------------
-- Traversal0Rep
---------------------------------------------------------------------

type ATraversal0 s t a b = Optic (Traversal0Rep a b) s t a b

type ATraversal0' s a = ATraversal0 s s a a

-- | The `Traversal0Rep` profunctor precisely characterizes an 'Traversal0'.
data Traversal0Rep a b s t = Traversal0Rep (s -> t + a) (s -> b -> t)

instance Profunctor (Traversal0Rep a b) where
  dimap f g (Traversal0Rep sta sbt) = Traversal0Rep
      (\a -> first g $ sta (f a))
      (\a v -> g (sbt (f a) v))

instance Strong (Traversal0Rep a b) where
  first' (Traversal0Rep sta sbt) = Traversal0Rep
      (\(a, c) -> first (,c) $ sta a)
      (\(a, c) v -> (sbt a v, c))

instance Choice (Traversal0Rep a b) where
  right' (Traversal0Rep sta sbt) = Traversal0Rep
      (\eca -> eassocl (second sta eca))
      (\eca v -> second (`sbt` v) eca)

instance Sieve (Traversal0Rep a b) (Index0 a b) where
  sieve (Traversal0Rep sta sbt) s = Index0 (sta s) (sbt s)

instance Representable (Traversal0Rep a b) where
  type Rep (Traversal0Rep a b) = Index0 a b

  tabulate f = Traversal0Rep (info0 . f) (values0 . f)

data Index0 a b r = Index0 (r + a) (b -> r)

values0 :: Index0 a b r -> b -> r
values0 (Index0 _ br) = br

info0 :: Index0 a b r -> r + a
info0 (Index0 a _) = a

instance Functor (Index0 a b) where
  fmap f (Index0 ra br) = Index0 (first f ra) (f . br)

instance Applicative (Index0 a b) where
  pure r = Index0 (Left r) (const r)
  liftA2 f (Index0 ra1 br1) (Index0 ra2 br2) = Index0 (eswap $ liftA2 f (eswap ra1) (eswap ra2)) (liftA2 f br1 br2)

---------------------------------------------------------------------
-- 'Cotraversal0Rep'
---------------------------------------------------------------------

-- | The 'Cotraversal0Rep' profunctor precisely characterizes 'Cotraversal0'.
--
newtype Cotraversal0Rep a b s t = Cotraversal0Rep { unCotraversal0Rep :: ((s -> t + a) -> b) -> t }

type ACotraversal0 s t a b = Optic (Cotraversal0Rep a b) s t a b

type ACotraversal0' s a = ACotraversal0 s s a a

instance Profunctor (Cotraversal0Rep a b) where
  dimap us tv (Cotraversal0Rep stabt) =
    Cotraversal0Rep $ \f -> tv (stabt $ \sta -> f (first tv . sta . us))

instance Closed (Cotraversal0Rep a b) where
  closed (Cotraversal0Rep stabt) =
    Cotraversal0Rep $ \f x -> stabt $ \sta -> f $ \xs -> first const $ sta (xs x)

instance Choice (Cotraversal0Rep a b) where
  left' (Cotraversal0Rep stabt) =
    Cotraversal0Rep $ \f -> Left $ stabt $ \sta -> f $ eassocl . fmap eswap . eassocr . first sta

{-todo
Corepresentable
Coapplicative (Corep)
-}

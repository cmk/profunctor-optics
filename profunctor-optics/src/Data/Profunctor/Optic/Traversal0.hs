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
  , ATraversal0 
  , ATraversal0'
  , traversal0
  , traversal0'
  , ixtraversal0
  , ixtraversal0'
  , traversal0Vl
  , ixtraversal0Vl
    -- * Carriers
  , Traversal0Rep(..)
    -- * Primitive operators
  , withTraversal0
    -- * Optics
  , nulled
  , inserted
  , selected
  , predicated
    -- * Operators
  , is
  , isnt
  , matches
) where

import Data.Bifunctor (first, second)
import Data.Bitraversable
import Data.List.Index
import Data.Map as Map
import Data.Semigroup.Bitraversable
import Data.Profunctor.Optic.Lens hiding (first, second, unit)
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Prism (prism)
import Data.Profunctor.Optic.Grate
import Data.Profunctor.Optic.Type
import Data.Semiring
import Control.Monad.Trans.State
import Data.Profunctor.Optic.Iso
import qualified Data.Bifunctor as B

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
-- >>> let catchOn :: Int -> Cxprism' Int (Maybe String) String ; catchOn n = cxjust $ \k -> if k==n then Just "caught" else Nothing
-- >>> let ixtraversed :: Ixtraversal Int [a] [b] a b ; ixtraversed = ixtraversalVl itraverse

---------------------------------------------------------------------
-- 'Traversal0' & 'Ixtraversal0'
---------------------------------------------------------------------

type ATraversal0 s t a b = Optic (Traversal0Rep a b) s t a b

type ATraversal0' s a = ATraversal0 s s a a

-- | Create a 'Traversal0' from a constructor and a matcheser.
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

-- | Obtain a 'Traversal0'' from a constructor and a matcheser function.
--
traversal0' :: (s -> Maybe a) -> (s -> a -> s) -> Traversal0' s a
traversal0' sa sas = flip traversal0 sas $ \s -> maybe (Left s) Right (sa s)

-- | TODO: Document
--
ixtraversal0 :: (s -> t + (i , a)) -> (s -> b -> t) -> Ixtraversal0 i s t a b
ixtraversal0 stia sbt = ixtraversal0Vl $ \point f s -> either point (fmap (sbt s) . uncurry f) (stia s)

-- | TODO: Document
--
ixtraversal0' :: (s -> Maybe (i , a)) -> (s -> a -> s) -> Ixtraversal0' i s a
ixtraversal0' sia = ixtraversal0 $ \s -> maybe (Left s) Right (sia s) 

-- | Transform a Van Laarhoven 'Traversal0' into a profunctor 'Traversal0'.
--
traversal0Vl :: (forall f. Functor f => (forall c. c -> f c) -> (a -> f b) -> s -> f t) -> Traversal0 s t a b
traversal0Vl f = dimap (\s -> (s,) <$> eswap (sat s)) (id ||| uncurry sbt) . right' . second'
  where
    sat = f Right Left
    sbt s b = runIdentity $ f Identity (\_ -> Identity b) s

-- | Transform an indexed Van Laarhoven 'Traversal0' into an indexed profunctor 'Traversal0'.
--
ixtraversal0Vl :: (forall f. Functor f => (forall c. c -> f c) -> (i -> a -> f b) -> s -> f t) -> Ixtraversal0 i s t a b
ixtraversal0Vl f = traversal0Vl $ \cc iab -> f cc (curry iab) . snd

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | TODO: Document
--
withTraversal0 :: ATraversal0 s t a b -> ((s -> t + a) -> (s -> b -> t) -> r) -> r
withTraversal0 o k = case o (Traversal0Rep Right $ const id) of Traversal0Rep x y -> k x y

---------------------------------------------------------------------
-- Common 'Traversal0's, 'Traversal's, 'Traversal1's, & 'Cotraversal1's
---------------------------------------------------------------------

-- | TODO: Document
--
nulled :: Traversal0' s a
nulled = traversal0 Left const 
{-# INLINE nulled #-}

-- | Obtain a 'Ixtraversal0'' from a pair of lookup and insert functions.
--
-- @
-- inserted (\i s -> flip 'Data.List.Index.ifind' s $ \n _ -> n == i) (\i a s -> 'Data.List.Index.modifyAt' i (const a) s) :: Int -> Ixtraversal0' Int [a] a
-- inserted 'Data.Map.lookupGT' 'Data.Map.insert' :: Ord i => i -> Ixtraversal0' i (Map i a) a
-- inserted 'Data.IntMap.lookupGT' 'Data.IntMap.insert' :: Int -> Ixtraversal0' Int (IntMap a) a
-- @
--
inserted :: (i -> s -> Maybe (i, a)) -> (i -> a -> s -> s) -> i -> Ixtraversal0' i s a
inserted isia iasa i = ixtraversal0Vl $ \point f s ->
  case isia i s of
    Nothing      -> point s
    Just (i', a) -> f i' a <&> \a -> iasa i' a s
{-# INLINE inserted #-}

-- | TODO: Document
--
-- See also 'Data.Profunctor.Optic.Prism.keyed'.
--
-- >>>  preview (selected even) (2, "hi")
-- Just "hi"
-- >>>  preview (selected even) (3, "hi")
-- Nothing
--
selected :: (a -> Bool) -> Traversal0' (a, b) b
selected p = traversal0 (\kv@(k,v) -> branch p kv v k) (\kv@(k,_) v' -> if p k then (k,v') else kv)
{-# INLINE selected #-}

-- | Filter result(s) that don't satisfy a predicate.
--
-- /Caution/: While this is a valid 'Traversal0', it is only a valid 'Traversal'
-- if the predicate always evaluates to 'True' on the targets of the 'Traversal'.
--
-- @
-- 'predicated' p ≡ 'traversal0Vl' $ \point f a -> if p a then f a else point a
-- @
--
-- >>> [1..10] ^.. folded . predicated even
-- [2,4,6,8,10]
--
-- See also 'Data.Profunctor.Optic.Prism.filtered'.
--
predicated :: (a -> Bool) -> Traversal0' a a
predicated p = traversal0 (branch' p) (flip const)
{-# INLINE predicated #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Check whether the optic is matchesed.
--
-- >>> is just Nothing
-- False
--
is :: ATraversal0 s t a b -> s -> Bool
is o = either (const False) (const True) . matches o
{-# INLINE is #-}

-- | Check whether the optic isn't matchesed.
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
-- 'Traversal0Rep'
---------------------------------------------------------------------

-- | The `Traversal0Rep` profunctor precisely characterizes an 'Traversal0'.
data Traversal0Rep a b s t = Traversal0Rep (s -> t + a) (s -> b -> t)

instance Profunctor (Traversal0Rep u v) where
  dimap f g (Traversal0Rep getter setter) = Traversal0Rep
      (\a -> first g $ getter (f a))
      (\a v -> g (setter (f a) v))

instance Strong (Traversal0Rep u v) where
  first' (Traversal0Rep getter setter) = Traversal0Rep
      (\(a, c) -> first (,c) $ getter a)
      (\(a, c) v -> (setter a v, c))

instance Choice (Traversal0Rep u v) where
  right' (Traversal0Rep getter setter) = Traversal0Rep
      (\eca -> eassocl (second getter eca))
      (\eca v -> second (`setter` v) eca)

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
  {-# INLINE fmap #-}

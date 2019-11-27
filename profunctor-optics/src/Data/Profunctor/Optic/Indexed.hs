{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE DeriveGeneric         #-}

module Data.Profunctor.Optic.Indexed where

{-
  , Index(..)
  , values
  , info 
  , Coindex(..)
  , trivial
-}

import Control.Monad (void)
import Data.Bifunctor
import Data.Bifunctor as B
import Data.Foldable
import Data.Profunctor.Closed
import Data.Profunctor.Monad
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Type
import Data.Profunctor.Strong
import Data.Profunctor.Traversing
import Data.Profunctor.Unsafe
import Data.Semiring
import Data.Tagged
import GHC.Generics (Generic)
import Prelude (Num(..))
import qualified Control.Arrow as Arrow
import qualified Control.Category as C
import qualified Prelude as Prelude

import Data.List.Index

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> :set -XTupleSections
-- >>> import Data.Monoid
-- >>> import Data.List.Index
-- >>> :load Data.Profunctor.Optic

---------------------------------------------------------------------
-- Index
---------------------------------------------------------------------

-- | An indexed store that characterizes a 'Data.Profunctor.Optic.Lens.Lens'
--
-- @'Index' a b r ≡ forall f. 'Functor' f => (a -> f b) -> f r@,
--
data Index a b r = Index a (b -> r)

values :: Index a b r -> b -> r
values (Index _ br) = br
{-# INLINE values #-}

info :: Index a b r -> a
info (Index a _) = a
{-# INLINE info #-}

instance Functor (Index a b) where
  fmap f (Index a br) = Index a (f . br)
  {-# INLINE fmap #-}

instance Profunctor (Index a) where
  dimap f g (Index a br) = Index a (g . br . f)
  {-# INLINE dimap #-}

instance a ~ b => Foldable (Index a b) where
  foldMap f (Index b br) = f . br $ b

---------------------------------------------------------------------
-- Coindex
---------------------------------------------------------------------

-- | An indexed continuation that characterizes a 'Data.Profunctor.Optic.Grate.Grate'
--
-- @'Coindex' a b k ≡ forall f. 'Functor' f => (f a -> b) -> f k@,
--
-- See also 'Data.Profunctor.Optic.Grate.zipWithFOf'.
--
-- 'Coindex' can also be used to compose indexed maps, folds, or traversals directly.
--
-- For example, using the @containers@ library:
--
-- @
--  Coindex mapWithKey :: Coindex (a -> b) (Map k a -> Map k b) k
--  Coindex foldMapWithKey :: Monoid m => Coindex (a -> m) (Map k a -> m) k
--  Coindex traverseWithKey :: Applicative t => Coindex (a -> t b) (Map k a -> t (Map k b)) k
-- @
--
newtype Coindex a b k = Coindex { runCoindex :: (k -> a) -> b } deriving Generic

-- | Change the @Monoid@ used to combine indices.
--
instance Functor (Coindex a b) where
  fmap kl (Coindex abk) = Coindex $ \la -> abk (la . kl)

instance a ~ b => Apply (Coindex a b) where
  (Coindex klab) <.> (Coindex abk) = Coindex $ \la -> klab $ \kl -> abk (la . kl) 

instance a ~ b => Applicative (Coindex a b) where
  pure k = Coindex ($k)
  (<*>) = (<.>)

trivial :: Coindex a b a -> b
trivial (Coindex f) = f id
{-# INLINE trivial #-}

-- | Lift a regular function into a coindexed function.
--
-- For example, to traverse two layers, keeping only the first index:
--
-- @
--  Coindex 'Data.Map.mapWithKey' % noindex 'Data.Map.map'
--    :: Monoid k =>
--       Coindex (a -> b) (Map k (Map j a) -> Map k (Map j b)) k
-- @
--
noindex :: Monoid k => (a -> b) -> Coindex a b k
noindex f = Coindex $ \a -> f (a mempty)

coindex :: Functor f => k -> (a -> b) -> Coindex (f a) (f b) k
coindex k ab = Coindex $ \kfa -> fmap ab (kfa k)
{-# INLINE coindex #-}


infixr 9 %

-- | Compose two coindexes.
--
-- When /k/ is a 'Monoid', 'Coindex' can be used to compose indexed traversals, folds,
-- views, and setters.
--
-- For example, to keep track of only the first index seen, use @Data.Monoid.First@:
--
-- @
--  fmap (First . pure) :: Coindex a b c -> Coindex a b (First c)
-- @
--
-- or keep track of all indices using a list:
--
-- @
--  fmap (:[]) :: Coindex a b c -> Coindex a b [c]
-- @
--
--
-- >>> runCoindex (Coindex imap % noindex fmap) (<>) [[1,1,1],[1,1,1]]
-- [[1,1,1],[2,2,2]]
-- >>> runCoindex (Coindex imap % Coindex imap) (<>) [[1,1,1],[1,1,1]]
-- [[1,2,3],[2,3,4]]
-- >>> let foi = fmap (First . pure) $ Coindex imap % Coindex imap
-- >>> runCoindex foi (\fi a -> (getFirst fi,a)) [[1,1,1],[1,1,1]]
-- [[(Just 0,1),(Just 1,1),(Just 2,1)],[(Just 1,1),(Just 2,1),(Just 3,1)]]
-- >>> let foi = fmap (:[]) $ Coindex imap % Coindex imap
--
{-
foi = fmap (:[]) $ Coindex imap % Coindex imap
λ> runCoindex foi (,) [[1,1],[1,1]]
[[([0],1),([1],1)],[([1],1),([2],1)]]
λ> runCoindex (foi % pure [0]) (,) [[1,1],[1,1]]
[[([0,0],1),([1,0],1)],[([1,0],1),([2,0],1)]]
-}

(%) :: Semigroup k => Coindex b c k -> Coindex a b k -> Coindex a c k
Coindex f % Coindex g = Coindex $ \b -> f $ \k1 -> g $ \k2 -> b (k1 <> k2)

---------------------------------------------------------------------
-- Ix & Cx
---------------------------------------------------------------------

type Ix' p a b = Ix p a a b

type Cx' p a b = Cx p a a b

reix :: Profunctor p => (i -> j) -> (Ix p i a b -> r) -> Ix p j a b -> r
reix ij = (. reindex ij)

reindex :: Profunctor p => (i -> j) -> Ix p j a b -> Ix p i a b
reindex ij = lmap (first' ij)

ixdimap :: Profunctor p => (c -> a) -> (b -> d) -> Ix p i a b -> Ix p i c d
ixdimap l r = dimap (fmap l) r

cxdimap :: Profunctor p => (c -> a) -> (b -> d) -> Cx p j a b -> Cx p j c d
cxdimap l r = dimap l (fmap r)

cxed :: Strong p => Iso (Cx p s s t) (Cx p j a b) (p s t) (p a b)
cxed = dimap cxjoin cxreturn

cxjoin :: Strong p => Cx p a a b -> p a b
cxjoin = peval

cxreturn :: Profunctor p => p a b -> Cx p j a b
cxreturn = rmap const

cxunit :: Strong p => Cx' p :-> p
cxunit p = dimap fork apply (first' p)

cxpastro :: Profunctor p => Iso (Cx' p a b) (Cx' p c d) (Pastro p a b) (Pastro p c d)
cxpastro = dimap (\p -> Pastro apply p fork) (\(Pastro l m r) -> dimap (fst . r) (\y a -> l (y, (snd (r a)))) m)

-- | 'Cx'' is freely strong.
--
-- See <https://r6research.livejournal.com/27858.html>.
--
cxfirst' :: Profunctor p => Cx' p a b -> Cx' p (a, c) (b, c)
cxfirst' = dimap fst (B.first @(,))

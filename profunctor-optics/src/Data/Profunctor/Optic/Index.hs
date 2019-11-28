{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE DeriveGeneric         #-}
module Data.Profunctor.Optic.Index ( 
    -- * Indexing
    (%)
  , ixinit
  , ixlast
  , reix
  , ixdimap
  , withIxrepn
    -- * Coindexing
  , (#)
  , cxinit
  , cxlast
  , recx
  , cxdimap
  , cxed
  , cxjoin
  , cxreturn
  , type Cx'
  , cxunit
  , cxpastro
  , cxfirst'
  , withCxrepn
    -- * Index
  , Index(..)
  , values
  , info
    -- * Coindex
  , Coindex(..)
  , trivial
  , noindex
  , coindex
  , (##)
) where

import Control.Monad (void)
import Data.Bifunctor
import Data.Bifunctor as B
import Data.Foldable
import Data.Semigroup
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
-- >>> import Data.Semigroup
-- >>> import Data.Semiring
-- >>> import Data.Map
-- >>> :load Data.Profunctor.Optic
-- >>> let ixtraversed :: Ord k => Ixtraversal k (Map k a) (Map k b) a b ; ixtraversed = ixtraversalVl traverseWithKey
-- >>> let foobar = fromList [(0::Int, fromList [(0,"foo"), (1,"bar")]), (1, fromList [(0,"baz"), (1,"bip")])]
-- >>> let exercises :: Map String (Map String Int); exercises = fromList [("Monday", fromList [("pushups", 10), ("crunches", 20)]), ("Wednesday", fromList [("pushups", 15), ("handstands", 3)]), ("Friday", fromList [("crunches", 25), ("handstands", 5)])] 

---------------------------------------------------------------------
-- Indexing
---------------------------------------------------------------------

infixr 8 %

-- | Compose two indexed traversals, combining indices.
--
-- Its precedence is one lower than that of function composition, which allows /./ to be nested in /%/.
--
-- If you only need the final index then use /./:
--
-- >>> ixlists (ixtraversed . ixtraversed) foobar
-- [(0,"foo"),(1,"bar"),(0,"baz"),(1,"bip")]
--
-- >>> ixlistsFrom (ixlast ixtraversed % ixlast ixtraversed) (Last 0) foobar & fmapped . first ..~ getLast
-- [(0,"foo"),(1,"bar"),(0,"baz"),(1,"bip")]
--
-- >>> ixlists (ixtraversed . ixtraversed) exercises
-- [("crunches",25),("handstands",5),("crunches",20),("pushups",10),("handstands",3),("pushups",15)]
--
-- >>> ixlists (ixtraversed % ixtraversed) exercises 
-- [("Fridaycrunches",25),("Fridayhandstands",5),("Mondaycrunches",20),("Mondaypushups",10),("Wednesdayhandstands",3),("Wednesdaypushups",15)]
--
(%) :: Semigroup i => IxrepnLike p i b1 b2 a1 a2 -> IxrepnLike p i c1 c2 b1 b2 -> IxrepnLike p i c1 c2 a1 a2
f % g = repn $ \ia1a2 (ic,c1) -> 
          withIxrepn g ic c1 $ \ib b1 -> 
            withIxrepn f ib b1 $ \ia a1 -> ia1a2 (ib <> ia, a1)
{-# INLINE (%) #-}

ixinit :: Profunctor p => IndexedOptic p i s t a b -> IndexedOptic p (First i) s t a b
ixinit = reix First getFirst

ixlast :: Profunctor p => IndexedOptic p i s t a b -> IndexedOptic p (Last i) s t a b
ixlast = reix Last getLast

-- | Map over the indices of an indexed optic.
--
-- >>> ixlists (ixtraversed . reix (<>10) id ixtraversed) foobar
-- [(10,"foo"),(11,"bar"),(10,"baz"),(11,"bip")]
--
-- See also 'Data.Profunctor.Optic.Iso.reixed'.
--
reix :: Profunctor p => (i -> j) -> (j -> i) -> IndexedOptic p i s t a b -> IndexedOptic p j s t a b
reix ij ji = (. lmap (first' ij)) . (lmap (first' ji) .)

ixdimap :: Profunctor p => (c -> a) -> (b -> d) -> Ix p i a b -> Ix p i c d
ixdimap l r = dimap (fmap l) r

withIxrepn :: Representable p => IxrepnLike p i s t a b -> i -> s -> (i -> a -> Rep p b) -> Rep p t
withIxrepn abst i s iab = (sieve . abst . tabulate $ uncurry iab) (i, s)

---------------------------------------------------------------------
-- Coindexing
---------------------------------------------------------------------

infixr 8 #

-- | Compose two coindexed traversals, combining indices.
--
-- Its precedence is one lower than that of function composition, which allows /./ to be nested in /#/.
--
-- If you only need the final index then use /./
--
(#) :: Semigroup k => CxrepnLike p k b1 b2 a1 a2 -> CxrepnLike p k c1 c2 b1 b2 -> CxrepnLike p k c1 c2 a1 a2
f # g = corepn $ \a1ka2 c1 kc -> 
          withCxrepn g c1 kc $ \b1 kb -> 
            withCxrepn f b1 kb $ \a1 ka -> a1ka2 a1 (kb <> ka)
{-# INLINE (#) #-}

cxinit :: Profunctor p => CoindexedOptic p k s t a b -> CoindexedOptic p (First k) s t a b
cxinit = recx First getFirst

cxlast :: Profunctor p => CoindexedOptic p k s t a b -> CoindexedOptic p (Last k) s t a b
cxlast = recx Last getLast

-- | Map over the indices of a coindexed optic.
--
-- See also 'Data.Profunctor.Optic.Iso.recxed'.
--
recx :: Profunctor p => (k -> l) -> (l -> k) -> CoindexedOptic p k s t a b -> CoindexedOptic p l s t a b
recx kl lk = (. rmap (. kl)) . (rmap (. lk) .)

cxdimap :: Profunctor p => (c -> a) -> (b -> d) -> Cx p k a b -> Cx p k c d
cxdimap l r = dimap l (fmap r)

cxed :: Strong p => Iso (Cx p s s t) (Cx p k a b) (p s t) (p a b)
cxed = dimap cxjoin cxreturn

cxjoin :: Strong p => Cx p a a b -> p a b
cxjoin = peval

cxreturn :: Profunctor p => p a b -> Cx p k a b
cxreturn = rmap const

type Cx' p a b = Cx p a a b

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

withCxrepn :: Corepresentable p => CxrepnLike p k s t a b -> Corep p s -> k -> (Corep p a -> k -> b) -> t
withCxrepn abst s k akb = (cosieve . abst $ cotabulate akb) s k

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
--  Coindex 'Data.Map.mapWithKey' ## noindex 'Data.Map.map'
--    :: Monoid k =>
--       Coindex (a -> b) (Map k (Map j a) -> Map k (Map j b)) k
-- @
--
noindex :: Monoid k => (a -> b) -> Coindex a b k
noindex f = Coindex $ \a -> f (a mempty)

coindex :: Functor f => k -> (a -> b) -> Coindex (f a) (f b) k
coindex k ab = Coindex $ \kfa -> fmap ab (kfa k)
{-# INLINE coindex #-}

infixr 9 ##

-- | Compose two coindexes.
--
-- When /k/ is a 'Monoid', 'Coindex' can be used to compose indexed traversals, folds, etc.
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
(##) :: Semigroup k => Coindex b c k -> Coindex a b k -> Coindex a c k
Coindex f ## Coindex g = Coindex $ \b -> f $ \k1 -> g $ \k2 -> b (k1 <> k2)

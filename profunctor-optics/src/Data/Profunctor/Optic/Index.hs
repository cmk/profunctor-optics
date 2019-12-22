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
  , iinit
  , ilast
  , reix
  , imap
  , withIxrepn
    -- * Coindexing
  , (#)
  , kinit
  , klast
  , recx
  , kmap
  , cxed
  , kjoin
  , kreturn
  , type Cx'
  , kunit
  , kpastro
  , kfirst'
  , withCxrepn
    -- * Index
  , Index(..)
  , vals
  , info
    -- * Coindex
  , Coindex(..)
  , trivial
  , noindex
  , coindex
  , (.#.)
    -- * Coindex
  , Conjoin(..)
) where

import Control.Arrow as Arrow
import Control.Category (Category)
import Control.Comonad
import Control.Monad
import Control.Monad.Fix
import Data.Profunctor.Closed
import Data.Profunctor.Rep
import Data.Profunctor.Sieve

import Data.Bifunctor as B
import Data.Foldable
import Data.Semigroup
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Types
import Data.Profunctor.Strong
import GHC.Generics (Generic)

import qualified Control.Category as C

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> :set -XTupleSections
-- >>> :set -XRankNTypes
-- >>> import Data.Semigroup
-- >>> import Data.Semiring
-- >>> import Data.Int.Instance ()
-- >>> import Data.Map
-- >>> :load Data.Profunctor.Optic
-- >>> let itraversed :: Ord k => Ixtraversal k (Map k a) (Map k b) a b ; itraversed = itraversalVl traverseWithKey
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
-- >>> ilists (itraversed . itraversed) exercises
-- [("crunches",25),("handstands",5),("crunches",20),("pushups",10),("handstands",3),("pushups",15)]
--
-- >>> ilists (itraversed % itraversed) exercises 
-- [("Fridaycrunches",25),("Fridayhandstands",5),("Mondaycrunches",20),("Mondaypushups",10),("Wednesdayhandstands",3),("Wednesdaypushups",15)]
--
-- If you only need the final index then use /./:
--
-- >>> ilists (itraversed . itraversed) foobar
-- [(0,"foo"),(1,"bar"),(0,"baz"),(1,"bip")]
--
-- This is identical to the more convoluted:
--
-- >>> ilistsFrom (ilast itraversed % ilast itraversed) (Last 0) foobar & fmapped . first' ..~ getLast
-- [(0,"foo"),(1,"bar"),(0,"baz"),(1,"bip")]
--
(%) :: Semigroup i => Representable p => IndexedOptic p i b1 b2 a1 a2 -> IndexedOptic p i c1 c2 b1 b2 -> IndexedOptic p i c1 c2 a1 a2
f % g = repn $ \ia1a2 (ic,c1) -> 
          withIxrepn g ic c1 $ \ib b1 -> 
            withIxrepn f ib b1 $ \ia a1 -> ia1a2 (ib <> ia, a1)
{-# INLINE (%) #-}

iinit :: Profunctor p => IndexedOptic p i s t a b -> IndexedOptic p (First i) s t a b
iinit = reix First getFirst

ilast :: Profunctor p => IndexedOptic p i s t a b -> IndexedOptic p (Last i) s t a b
ilast = reix Last getLast

-- | Map over the indices of an indexed optic.
--
-- >>> ilists (itraversed . reix (<>10) id itraversed) foobar
-- [(10,"foo"),(11,"bar"),(10,"baz"),(11,"bip")]
--
-- See also 'Data.Profunctor.Optic.Iso.reixed'.
--
reix :: Profunctor p => (i -> j) -> (j -> i) -> IndexedOptic p i s t a b -> IndexedOptic p j s t a b
reix ij ji = (. lmap (first' ij)) . (lmap (first' ji) .)

-- >>> ilists (itraversed . imap head pure) [[1,2,3],[4,5,6]]
-- [(0,1),(1,4)]
imap :: Profunctor p => (s -> a) -> (b -> t) -> IndexedOptic p i s t a b
imap sa bt = dimap (fmap sa) bt

withIxrepn :: Representable p => IndexedOptic p i s t a b -> i -> s -> (i -> a -> Rep p b) -> Rep p t
withIxrepn abst i s iab = (sieve . abst . tabulate $ uncurry iab) (i, s)

---------------------------------------------------------------------
-- Coindexing
---------------------------------------------------------------------

infixr 8 #

-- | Compose two coindexed traversals, combining indices.
--
-- Its precedence is one lower than that of function composition, which allows /./ to be nested in /#/.
--
-- If you only need the final index then use /./.
--
(#) :: Semigroup k => Corepresentable p => CoindexedOptic p k b1 b2 a1 a2 -> CoindexedOptic p k c1 c2 b1 b2 -> CoindexedOptic p k c1 c2 a1 a2
f # g = corepn $ \a1ka2 c1 kc -> 
          withCxrepn g c1 kc $ \b1 kb -> 
            withCxrepn f b1 kb $ \a1 ka -> a1ka2 a1 (kb <> ka)
{-# INLINE (#) #-}

kinit :: Profunctor p => CoindexedOptic p k s t a b -> CoindexedOptic p (First k) s t a b
kinit = recx First getFirst

klast :: Profunctor p => CoindexedOptic p k s t a b -> CoindexedOptic p (Last k) s t a b
klast = recx Last getLast

-- | Map over the indices of a coindexed optic.
--
-- See also 'Data.Profunctor.Optic.Iso.recxed'.
--
recx :: Profunctor p => (k -> l) -> (l -> k) -> CoindexedOptic p k s t a b -> CoindexedOptic p l s t a b
recx kl lk = (. rmap (. kl)) . (rmap (. lk) .)

kmap :: Profunctor p => (s -> a) -> (b -> t) -> CoindexedOptic p k s t a b 
kmap sa bt = dimap sa (fmap bt)

-- | Generic type for a co-indexed optic.
type Cx p k a b = p a (k -> b)

type Cx' p a b = Cx p a a b

cxed :: Strong p => Iso (Cx p s s t) (Cx p k a b) (p s t) (p a b)
cxed = dimap kjoin kreturn

kjoin :: Strong p => Cx p a a b -> p a b
kjoin = peval

kreturn :: Profunctor p => p a b -> Cx p k a b
kreturn = rmap const

kunit :: Strong p => Cx' p :-> p
kunit p = dimap fork apply (first' p)

kpastro :: Profunctor p => Iso (Cx' p a b) (Cx' p c d) (Pastro p a b) (Pastro p c d)
kpastro = dimap (\p -> Pastro apply p fork) (\(Pastro l m r) -> dimap (fst . r) (\y a -> l (y, (snd (r a)))) m)

-- | 'Cx'' is freely strong.
--
-- See <https://r6research.livejournal.com/27858.html>.
--
kfirst' :: Profunctor p => Cx' p a b -> Cx' p (a, c) (b, c)
kfirst' = dimap fst (B.first @(,))

withCxrepn :: Corepresentable p => CoindexedOptic p k s t a b -> Corep p s -> k -> (Corep p a -> k -> b) -> t
withCxrepn abst s k akb = (cosieve . abst $ cotabulate akb) s k

---------------------------------------------------------------------
-- Index
---------------------------------------------------------------------

-- | An indexed store that characterizes a 'Data.Profunctor.Optic.Lens.Lens'
--
-- @'Index' a b s ≡ forall f. 'Functor' f => (a -> f b) -> f s@,
--
-- See also 'Data.Profunctor.Optic.Lens.withLensVl'.
--
data Index a b s = Index a (b -> s) deriving Generic

vals :: Index a b s -> b -> s
vals (Index _ bs) = bs
{-# INLINE vals #-}

info :: Index a b s -> a
info (Index a _) = a
{-# INLINE info #-}

instance Functor (Index a b) where
  fmap f (Index a bs) = Index a (f . bs)
  {-# INLINE fmap #-}

instance Profunctor (Index a) where
  dimap f g (Index a bs) = Index a (g . bs . f)
  {-# INLINE dimap #-}

instance a ~ b => Foldable (Index a b) where
  foldMap f (Index b bs) = f . bs $ b

---------------------------------------------------------------------
-- Coindex
---------------------------------------------------------------------

-- | An indexed continuation that characterizes a 'Data.Profunctor.Optic.Grate.Grate'
--
-- @'Coindex' a b s ≡ forall f. 'Functor' f => (f a -> b) -> f s@,
--
-- See also 'Data.Profunctor.Optic.Grate.withGrateVl'.
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
newtype Coindex a b s = Coindex { runCoindex :: (s -> a) -> b } deriving Generic

instance Functor (Coindex a b) where
  fmap sl (Coindex abs) = Coindex $ \la -> abs (la . sl)

instance a ~ b => Apply (Coindex a b) where
  (Coindex slab) <.> (Coindex abs) = Coindex $ \la -> slab $ \sl -> abs (la . sl) 

instance a ~ b => Applicative (Coindex a b) where
  pure s = Coindex ($s)
  (<*>) = (<.>)

trivial :: Coindex a b a -> b
trivial (Coindex f) = f id
{-# INLINE trivial #-}

-- | Lift a regular function into a coindexed function.
--
-- For example, to traverse two layers, keeping only the first index:
--
-- @
--  Coindex 'Data.Map.mapWithKey' .#. noindex 'Data.Map.map'
--    :: Monoid k =>
--       Coindex (a -> b) (Map k (Map j a) -> Map k (Map j b)) k
-- @
--
noindex :: Monoid s => (a -> b) -> Coindex a b s
noindex f = Coindex $ \a -> f (a mempty)

coindex :: Functor f => s -> (a -> b) -> Coindex (f a) (f b) s
coindex s ab = Coindex $ \sfa -> fmap ab (sfa s)
{-# INLINE coindex #-}

infixr 9 .#.

-- | Compose two coindexes.
--
-- When /s/ is a 'Monoid', 'Coindex' can be used to compose indexed traversals, folds, etc.
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
(.#.) :: Semigroup s => Coindex b c s -> Coindex a b s -> Coindex a c s
Coindex f .#. Coindex g = Coindex $ \b -> f $ \s1 -> g $ \s2 -> b (s1 <> s2)

---------------------------------------------------------------------
-- Conjoin
---------------------------------------------------------------------

-- '(->)' is simultaneously both indexed and co-indexed.
newtype Conjoin j a b = Conjoin { unConjoin :: j -> a -> b }

instance Functor (Conjoin j a) where
  fmap g (Conjoin f) = Conjoin $ \j a -> g (f j a)
  {-# INLINE fmap #-}

instance Apply (Conjoin j a) where
  Conjoin f <.> Conjoin g = Conjoin $ \j a -> f j a (g j a)
  {-# INLINE (<.>) #-}

instance Applicative (Conjoin j a) where
  pure b = Conjoin $ \_ _ -> b
  {-# INLINE pure #-}
  Conjoin f <*> Conjoin g = Conjoin $ \j a -> f j a (g j a)
  {-# INLINE (<*>) #-}

instance Monad (Conjoin j a) where
  return = pure
  {-# INLINE return #-}
  Conjoin f >>= k = Conjoin $ \j a -> unConjoin (k (f j a)) j a
  {-# INLINE (>>=) #-}

instance MonadFix (Conjoin j a) where
  mfix f = Conjoin $ \ j a -> let o = unConjoin (f o) j a in o
  {-# INLINE mfix #-}

instance Profunctor (Conjoin j) where
  dimap ab cd jbc = Conjoin $ \j -> cd . unConjoin jbc j . ab
  {-# INLINE dimap #-}
  lmap ab jbc = Conjoin $ \j -> unConjoin jbc j . ab
  {-# INLINE lmap #-}
  rmap bc jab = Conjoin $ \j -> bc . unConjoin jab j
  {-# INLINE rmap #-}

instance Closed (Conjoin j) where
  closed (Conjoin jab) = Conjoin $ \j xa x -> jab j (xa x)

instance Costrong (Conjoin j) where
  unfirst (Conjoin jadbd) = Conjoin $ \j a -> let
      (b, d) = jadbd j (a, d)
    in b

instance Sieve (Conjoin j) ((->) j) where
  sieve = flip . unConjoin
  {-# INLINE sieve #-}

instance Representable (Conjoin j) where
  type Rep (Conjoin j) = (->) j
  tabulate = Conjoin . flip
  {-# INLINE tabulate #-}

instance Cosieve (Conjoin j) ((,) j) where
  cosieve = uncurry . unConjoin
  {-# INLINE cosieve #-}

instance Corepresentable (Conjoin j) where
  type Corep (Conjoin j) = (,) j
  cotabulate = Conjoin . curry
  {-# INLINE cotabulate #-}

instance Choice (Conjoin j) where
  right' = right
  {-# INLINE right' #-}

instance Strong (Conjoin j) where
  second' = Arrow.second
  {-# INLINE second' #-}

instance Category (Conjoin j) where
  id = Conjoin (const id)
  {-# INLINE id #-}
  Conjoin f . Conjoin g = Conjoin $ \j -> f j . g j
  {-# INLINE (.) #-}

instance Arrow (Conjoin j) where
  arr f = Conjoin (\_ -> f)
  {-# INLINE arr #-}
  first f = Conjoin (Arrow.first . unConjoin f)
  {-# INLINE first #-}
  second f = Conjoin (Arrow.second . unConjoin f)
  {-# INLINE second #-}
  Conjoin f *** Conjoin g = Conjoin $ \j -> f j *** g j
  {-# INLINE (***) #-}
  Conjoin f &&& Conjoin g = Conjoin $ \j -> f j &&& g j
  {-# INLINE (&&&) #-}

instance ArrowChoice (Conjoin j) where
  left f = Conjoin (left . unConjoin f)
  {-# INLINE left #-}
  right f = Conjoin (right . unConjoin f)
  {-# INLINE right #-}
  Conjoin f +++ Conjoin g = Conjoin $ \j -> f j +++ g j
  {-# INLINE (+++)  #-}
  Conjoin f ||| Conjoin g = Conjoin $ \j -> f j ||| g j
  {-# INLINE (|||) #-}

instance ArrowApply (Conjoin j) where
  app = Conjoin $ \i (f, b) -> unConjoin f i b
  {-# INLINE app #-}

instance ArrowLoop (Conjoin j) where
  loop (Conjoin f) = Conjoin $ \j b -> let (c,d) = f j (b, d) in c
  {-# INLINE loop #-}

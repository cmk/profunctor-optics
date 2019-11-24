{-# LANGUAGE UndecidableInstances #-}
{-# Language FunctionalDependencies #-}
{-# Language AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE QuantifiedConstraints         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}

module Data.Profunctor.Optic.Indexed where

{-
  , Index(..)
  , values
  , info 
  , Coindex(..)
  , trivial
-}

import qualified Control.Arrow as Arrow
import Control.Monad (void)
import Data.Profunctor.Traversing
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Import
{-
import Data.Profunctor.Optic.Iso
--import Data.Profunctor.Optic.Lens
import Data.Profunctor.Optic.Prism
import Data.Profunctor.Optic.Repn
import Data.Profunctor.Optic.Setter
import Data.Profunctor.Optic.Fold
import Data.Profunctor.Optic.View
-}

import Data.Profunctor.Strong
import Data.Profunctor.Closed
import Data.Bifunctor
import qualified Prelude as Prelude

import Data.Profunctor.Unsafe
import Data.Foldable
import qualified Control.Category as C


import Data.Tagged
import Prelude (Num(..))
import GHC.Generics (Generic)
import Data.Semiring
import Data.Bifunctor as B
import Data.Profunctor.Monad

import Data.List.Index

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
-- 'Ix'
---------------------------------------------------------------------

type Ix' p a b = Ix p a a b

type Cx' p a b = Cx p a a b



--todo
--try CoindexedOptic w/ Co-things, better fit for the type and maybe work w/ Coindex?

--works but ..
--ofoldMapOf :: CoindexedOptic Tagged i s t a b -> (i -> b) -> (i -> t)
--ofoldMapOf o f = unTagged $ o $ Tagged f

--works but ..
--ofoldMapOf :: CoindexedOptic (Forget r) i s t a b -> (a -> r) -> s -> r
--ofoldMapOf o f = runForget $ o $ Forget f


--ofoldMapOf ::  (Forget r a (i -> b) -> Forget r s (i -> t)) -> ((i -> a) -> r) -> s -> r
--ofoldMapOf o f = runForget $ o $ Forget f 

--ofoldMapOf (oxo.oxo) :: (Traversable t1, Traversable t2) => ((i -> t1 (t2 b)) -> c) -> (i -> b) -> c

--reviews :: MonadReader b m => AReview t b -> (t -> r) -> m r
--reviews o f = asks (f . unTagged #. o .# Tagged)

--cofoldMapOf :: ACofold r t b -> (r -> b) -> r -> t
--cofoldMapOf o = (.# Const) #. runCostar #. o .# Costar .# (.# getConst)

--jfoldMapOf :: CoindexedOptic Tagged j s t a b -> ((j -> t) -> r) -> b -> r



ireturn :: Profunctor p => Optic p s t a b -> IndexedOptic p i s t a b
ireturn = undefined 

unindex :: Profunctor p => IndexedOptic p i s t a b -> Optic p s t a b
unindex o = undefined -- o . dimap snd id

asindex :: Profunctor p => IndexedOptic p i s t a b -> Optic p s t i b
asindex o = undefined -- o . dimap fst id

jreturn :: Profunctor p => p a b -> Cx p j a b
jreturn = rmap const

jjoin :: Strong p => Cx p a a b -> p a b
jjoin = peval

jxed :: Strong p => Iso (Cx p s s t) (Cx p j a b) (p s t) (p a b)
jxed = dimap jjoin jreturn

--jdimap :: Profunctor p => Profunctor q => (a -> b) -> (c -> d) -> p b (q b c) -> p a (q a d)
--jdimap l r = dimap l (dimap l r)

jdimap :: Profunctor p => (c -> a) -> (b -> d) -> Cx p j a b -> Cx p j c d
jdimap l r = dimap l (fmap r)

-- | 'Cx'' is freely strong.
--
-- See <https://r6research.livejournal.com/27858.html>.
--
jfirst' :: Profunctor p => Cx' p a b -> Cx' p (a, c) (b, c)
jfirst' = dimap fst (B.first @(,))
{-# INLINE jfirst' #-}

junit :: Strong p => Cx' p :-> p
junit p = dimap fork apply (first' p)

jpastro :: Profunctor p => Iso (Cx' p a b) (Cx' p c d) (Pastro p a b) (Pastro p c d)
jpastro = dimap (\p -> Pastro apply p fork) (\(Pastro l m r) -> dimap (fst . r) (\y a -> l (y, (snd (r a)))) m)

--type IndexedOptic p i s t a b = p (i , a) b -> p (i , s) t

--deltaIxed
--deltaCx


--deltaIx
reindex :: Profunctor p => (i -> j) -> Ix p j a b -> Ix p i a b
reindex ij = lmap (first' ij)

--reix :: Profunctor p => (i -> j) -> (a1 -> Ix p j a2 b) -> a1 -> Ix p i a2 b
reix :: Profunctor p => (i -> j) -> (Ix p i a b -> r) -> Ix p j a b -> r
reix ij = (. reindex ij)


--recx ij = 
idimap :: Profunctor p => (c -> a) -> (b -> d) -> Ix p i a b -> Ix p i c d
--idimap :: Profunctor p => Functor f => Functor g => (c -> a) -> (b -> d) -> p (f a) (g b) -> p (f c) (g d)
idimap l r = dimap (fmap l) r




{-
ilmap :: Profunctor p => Functor f => (a -> b) -> p (f b) c -> p (f a) c
ilmap f = lmap (fmap f)

irmap :: Profunctor p => Functor f => (c -> d) -> p a (f c) -> p a (f d)
irmap f = rmap (fmap f)
-}



{-


--apply
assocr' :: (a -> b, c) -> a -> (b, c)
assocr' (ab, c) = (,c) . ab


reindex :: Profunctor p => (i -> j) -> Ix p j a b -> Ix p i a b
reindex ij = over (dimap runIx Ix) $ lmap (first' ij)

--ifirst . closed :: (Strong p, Closed p) => p a b -> p (i -> a, c) (i -> (b, c))

newtype Ix p i a b = Ix { runIx :: p (i , a) b } deriving Generic

instance Profunctor p => Profunctor (Ix p i) where
  dimap f g (Ix p) = Ix (dimap (fmap f) g p)

instance Strong p => Strong (Ix p i) where
  first' (Ix p) = Ix $ lmap assocl (first' p)

instance Choice p => Choice (Ix p i) where
  left' (Ix p) = Ix $ lmap assocl' (left' p)

instance Sieve p f => Sieve (Ix p i) (Star f i) where
  sieve p a = Star $ (flip . curry . sieve $ runIx p) a

instance Representable p => Representable (Ix p i) where
  type Rep (Ix p i) = (Star (Rep p) i)
  tabulate aifb = Ix . tabulate . uncurry . flip $ runStar . aifb

newtype StrongT p s t = StrongT (p s (s -> t))

instance Profunctor p => Profunctor (StrongT p) where
  dimap l r (StrongT p) = StrongT (dimap l (dimap l r) p)

instance Profunctor p => Strong (StrongT p) where
  first' (StrongT p) = StrongT (dimap fst first p)

instance ProfunctorFunctor StrongT where
  promap eta (StrongT p) = StrongT (eta p)

instance ProfunctorMonad StrongT where
  proreturn p = StrongT (rmap const p)
  
  projoin (StrongT p) = peval p


-}



-- | A function with access to a index. This constructor may be useful when you need to store
-- an 'Indexable' in a container to avoid @ImpredicativeTypes@.
--
-- @index :: Indexed i a b -> i -> a -> b@
newtype Indexed i a b = Indexed { runIndexed :: i -> a -> b }

--conjoined instance
distrib :: Functor f => Indexed i a b -> Indexed i (f a) (f b)
distrib (Indexed iab) = Indexed $ \i fa -> iab i <$> fa

instance Functor (Indexed i a) where
  fmap g (Indexed f) = Indexed $ \i a -> g (f i a)
  {-# INLINE fmap #-}

instance Apply (Indexed i a) where
  Indexed f <.> Indexed g = Indexed $ \i a -> f i a (g i a)
  {-# INLINE (<.>) #-}

instance Applicative (Indexed i a) where
  pure b = Indexed $ \_ _ -> b
  {-# INLINE pure #-}
  Indexed f <*> Indexed g = Indexed $ \i a -> f i a (g i a)
  {-# INLINE (<*>) #-}

instance Monad (Indexed i a) where
  return = pure
  {-# INLINE return #-}
  Indexed f >>= k = Indexed $ \i a -> runIndexed (k (f i a)) i a
  {-# INLINE (>>=) #-}

{-
instance MonadFix (Indexed i a) where
  mfix f = Indexed $ \ i a -> let o = runIndexed (f o) i a in o
  {-# INLINE mfix #-}
-}

instance Profunctor (Indexed i) where
  dimap ab cd ibc = Indexed $ \i -> cd . runIndexed ibc i . ab
  {-# INLINE dimap #-}
  lmap ab ibc = Indexed $ \i -> runIndexed ibc i . ab
  {-# INLINE lmap #-}
  rmap bc iab = Indexed $ \i -> bc . runIndexed iab i
  {-# INLINE rmap #-}
{-
-- #ifndef SAFE
  ( .# ) ibc _ = coerce ibc
  {-# INLINE ( .# ) #-}
  ( #. ) _ = coerce'
  {-# INLINE ( #. ) #-}
-- #endif
-}

instance Closed (Indexed i) where
  closed (Indexed iab) = Indexed $ \i xa x -> iab i (xa x)

instance Costrong (Indexed i) where
  unfirst (Indexed iadbd) = Indexed $ \i a -> let
      (b, d) = iadbd i (a, d)
    in b

instance Sieve (Indexed i) ((->) i) where
  sieve = flip . runIndexed
  {-# INLINE sieve #-}

instance Representable (Indexed i) where
  type Rep (Indexed i) = (->) i
  tabulate = Indexed . flip
  {-# INLINE tabulate #-}

instance Cosieve (Indexed i) ((,) i) where
  cosieve = uncurry . runIndexed
  {-# INLINE cosieve #-}

instance Corepresentable (Indexed i) where
  type Corep (Indexed i) = (,) i
  cotabulate = Indexed . curry
  {-# INLINE cotabulate #-}

instance Strong (Indexed i) where
  second' f = Indexed (Arrow.second . runIndexed f)
  {-# INLINE second' #-}

{-
instance Choice (Indexed i) where
  right' = Arrow.right
  {-# INLINE right' #-}

instance Category (Indexed i) where
  id = Indexed (const id)
  {-# INLINE id #-}
  Indexed f . Indexed g = Indexed $ \i -> f i . g i
  {-# INLINE (.) #-}

instance Arrow (Indexed i) where
  arr f = Indexed (\_ -> f)
  {-# INLINE arr #-}
  first f = Indexed (Arrow.first . runIndexed f)
  {-# INLINE first #-}
  second f = Indexed (Arrow.second . runIndexed f)
  {-# INLINE second #-}
  Indexed f *** Indexed g = Indexed $ \i -> f i *** g i
  {-# INLINE (***) #-}
  Indexed f &&& Indexed g = Indexed $ \i -> f i &&& g i
  {-# INLINE (&&&) #-}

instance ArrowChoice (Indexed i) where
  left f = Indexed (left . runIndexed f)
  {-# INLINE left #-}
  right f = Indexed (right . runIndexed f)
  {-# INLINE right #-}
  Indexed f +++ Indexed g = Indexed $ \i -> f i +++ g i
  {-# INLINE (+++)  #-}
  Indexed f ||| Indexed g = Indexed $ \i -> f i ||| g i
  {-# INLINE (|||) #-}

instance ArrowApply (Indexed i) where
  app = Indexed $ \ i (f, b) -> runIndexed f i b
  {-# INLINE app #-}

instance ArrowLoop (Indexed i) where
  loop (Indexed f) = Indexed $ \i b -> let (c,d) = f i (b, d) in c
  {-# INLINE loop #-}
-}


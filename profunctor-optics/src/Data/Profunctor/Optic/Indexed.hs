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

import Data.Profunctor.Traversing
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Iso
--import Data.Profunctor.Optic.Lens
import Data.Profunctor.Optic.Prism
import Data.Profunctor.Optic.Repn
import Data.Profunctor.Optic.Setter
import Data.Profunctor.Strong
import Data.Profunctor.Closed
import Data.Bifunctor
import qualified Prelude as Prelude
import Data.Monoid
import Data.Profunctor.Unsafe
import Data.Foldable
import Data.Profunctor.Optic.Traversal
import Data.Profunctor.Optic.Grate
import qualified Control.Category as C

import Data.Tagged
import Prelude (Num(..))
import GHC.Generics (Generic)


import Data.Bifunctor as B
import Data.Profunctor.Monad

{-
Reader m 
itraversed :: (TraversableWithIndex i t) => IndexedOptic p r (i -> r) (t a) (t b) a b
itraversed = undefined

itraversed' :: (TraversableWithIndex i t) => IndexedOptic p i (i -> j) (t a) (t b) a b
itraversed' = undefined


λ> :t itraversed . itraversed
itraversed . itraversed
  :: (TraversableWithIndex i1 t1, TraversableWithIndex i2 t2) =>
     p r a b -> p (i1 -> i2 -> r) (t1 (t2 a)) (t1 (t2 b))

λ> :t itraversed' . itraversed'
itraversed' . itraversed'
  :: (TraversableWithIndex i t1,
      TraversableWithIndex (i -> j1) t2) =>
     p i a b -> p ((i -> j1) -> j2) (t2 (t1 a)) (t2 (t1 b))

type IndexedOptic p i o s t a b = p i a b -> p o s t
--type IndexedOptic p i o s t a b = p (a , i) b -> p (s , o) t
--type IndexedOptic' p i o s a = IndexedOptic p i (o -> i) s s a a

--type IndexedOptic p i o s t a b = p a (i -> b) -> p s (o -> t)

itraversed' :: (TraversableWithIndex i t) => IndexedOptic p i (i -> j) (t a) (t b) a b
itraversed' = undefined

itraversing :: (forall f. Applicative f => (i -> a -> f b) -> s -> f t) -> IxTravesal i s t a b
itraversing itr = traversing (\f s -> itr (curry f) s)

M.traverseWithKey :: Applicative t => (k -> a -> t b) -> Map k a -> t (Map k b)

itraversing M.traverseWithKey
  :: (Choice p, Applicative (Rep p), Representable p) =>
     IndexedOptic p i (Map i a) (Map i b) a b

λ>  foo = grate (. runCoindex)
λ> :t foo
foo :: Closed p => Optic p (i -> a1) (Coindex a1 a2 i -> c) a2 c
λ> :t constOf foo
constOf foo :: c -> Coindex a1 a2 i -> c
λ> :t zipWithOf foo
zipWithOf foo
  :: (a2 -> a2 -> c)
     -> (i -> a1) -> (i -> a1) -> Coindex a1 a2 i -> c

withCoindex :: Coindex a b i -> (forall f. Functor f => ((f a -> b) -> f i) -> r) -> r
withCoindex i = undefined

closingf :: (Representable p, Distributive (Rep p), Functor f) =>
                  (((i1 -> f b) -> f b) -> d) -> p i2 i1 -> p i2 d
-}

-- | TODO: Document
--
--closingf :: Functor f => (((s -> f a) -> f b) -> t) -> Setter s t a b
--closingf f = dimap index' (f . runCoindex) . lift collect


-- | A wrapper for a mapping or traversal function which uses an index.
--
-- For example, using the @containers@ library:
--
-- @
--  index mapWithKey
--    :: Coindex (a -> b) (Map i a -> Map i b) i
--  index foldMapWithKey
--    :: Monoid m => Coindex (a -> m) (Map i a -> m) i
--  index traverseWithKey
--    :: Applicative t => Coindex (a -> t b) (Map i a -> t (Map i b)) i
-- @
--
index :: ((i -> a) -> b) -> Coindex a b i
index = Coindex

index' :: Functor f => i -> (a -> b) -> Coindex (f a) (f b) i
index' i ab = Coindex $ \ifa -> fmap ab (ifa i)


foo :: Functor f => (f a -> b) -> f i -> (i -> a) -> b
foo fab fi ia = fab (fmap ia fi)

bar :: Functor f => i -> (a -> b) -> (i -> f a) -> f b
bar i ab ifa = fmap ab (ifa i)

baz :: ((Coindex a1 b1 a1 -> b1) -> Coindex a3 b2 i -> a2) -> ((i -> a3) -> b2) -> a2
baz o = (o trivial) . Coindex



{-
vlgrate :: (forall f. Functor f => (f a -> b) -> f s -> t) -> Grate s t a b 
vlgrate o = dimap (curry eval) (baz o) . closed

bar :: Functor f => (((a -> b) -> t1) -> t2) -> (f b -> t1) -> f a -> t2
bar k fbt fa = k (foo fbt fa)


baz :: Functor f => (((i -> a) -> b) -> t1) -> (((f a -> b) -> f i -> t1) -> t2) -> t2
baz :: (((i -> a) -> b) -> r) -> (forall f. Functor f => (f a -> b) -> f i -> r) -> r
baz iabr k = k $ \fab fi -> iabr (foo fab fi)

(f a -> b) -> f s -> t

\o -> (info &&& values) . o (flip Indexed id)
  :: ((a1 -> Indexed a1 r1 r1) -> a2 -> Indexed b1 b r2)
     -> a2 -> (b1, b -> r2)


ok o = dimap (runCoindex . o anindex) (flip ($)) (uncurry id . swap) 
  :: ((i1 -> Coindex a1 a1 i1) -> a2 -> Coindex a3 b i2)
     -> a2 -> (i2 -> a3) -> b

\o -> anindex . o runCoindex
vllens :: (forall f. Functor f => (a -> f b) -> s -> f t) -> Lens s t a b
vllens o = dimap ((info &&& values) . o (flip Indexed id)) (uncurry id . swap) . first'


-}


-- | Lift a regular function into an indexed function.
--
-- For example, to traverse two layers, keeping only the first index:
--
-- @
--  index 'Data.Map.mapWithKey' % noindex 'Data.Map.map'
--    :: Monoid i =>
--       Coindex (a -> b) (Map i (Map k a) -> Map i (Map k b)) i
-- @
--
noindex :: Monoid i => (a -> b) -> Coindex a b i
noindex f = Coindex $ \a -> f (a mempty)

-- | Lift a particular index value into an 'Coindex'.
--
anindex :: i -> Coindex a a i
anindex i = Coindex ($i)

-- | The identity 'Coindex' for a 'Monoid' /i/.
--
idx :: Monoid i => Coindex a a i
idx = anindex mempty
{-
λ> :t zipWithOf indexed (,)
zipWithOf indexed (,) :: s -> s -> Coindex a (a, a) s

λ> :t constOf indexed
constOf indexed :: b -> Coindex a b s

λ> :t constOf (indexed . indexed)
constOf (indexed . indexed) :: b -> Coindex a1 (Coindex a2 b a1) s
-}

indexed :: Grate i (Coindex a b i) a b
indexed = grate index


infixr 9 %
-- | Compose two 'Coindex's.
--
-- When /i/ is a 'Monoid', 'Coindex' can be used to compose indexed traversals, folds,
-- and setters.
--
-- For example, to keep track of only the first index seen, use @Data.Monoid.First@:
--
-- @
--  fmap (First . pure)
--    :: Coindex a b i -> Coindex a b (First i)
-- @
--
-- or keep track of all indices using a list
--
-- @
--  fmap (: [])
--    :: Coindex a b i -> Coindex a b [i]
-- @
--
-- @
--  index 'Data.Map.mapWithKey' % index 'Data.Map.mapWithKey'
--    :: Monoid i =>
--       Coindex (a -> b) (Map i (Map i a) -> Map i (Map i b)) i
-- @
--
-- and then applied using 'runCoindex':
--
-- @
--  runCoindex $ index 'Data.Map.mapWithKey' % index 'Data.Map.mapWithKey'
--    :: Monoid i => (i -> a -> b) -> Map i (Map i a) -> Map i (Map i b)
-- @
--
(%) :: Semigroup i => Coindex b c i -> Coindex a b i -> Coindex a c i
Coindex f % Coindex g = Coindex $ \b -> f $ \i1 -> g $ \i2 -> b (i1 <> i2)



---------------------------------------------------------------------
-- 'Ix'
---------------------------------------------------------------------




--http://hackage.haskell.org/package/indextype-0.3.0.1/docs/Control-IndexT.html
--http://hackage.haskell.org/package/with-index-0.1.0.0/docs/Data-WithIndex.html
--type IndexedOptic p i o s t a b = p i a b -> p o s t
--type IndexedOptic p i o s t a b = p (a , i) b -> p (s , o) t
--type IndexedOptic' p i o s a = IndexedOptic p i (o -> i) s s a a

--type IndexedOptic p i o s t a b = p a (i -> b) -> p s (o -> t)

{-
type IndexedOptic p i o s t a b = p (i , a) b -> p s t

type Ixlens i o s t a b = forall p. Ixlenslike p i o s t a b
type Ixlenslike p i o s t a b = Strong p => IndexedOptic p i o s t a b

type IRepnlike p i o s t a b = Representable p => IndexedOptic p i o s t a b
type IxTravesal i o s t a b = forall p. Choice p => Applicative (Rep p) => IRepnlike p i o s t a b
-}








--todo
--remove PrimFoo?
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
ofoldMapOf :: CoindexedOptic Tagged j s t a b -> ((j -> t) -> c) -> (j -> b) -> c
ofoldMapOf o f = f . unTagged . o . Tagged

reindexed :: CoindexedOptic Tagged j s t a b -> Coindex t c j -> Coindex b c j
reindexed o (Coindex f) = Coindex $ ofoldMapOf o f

--ifoldMapOf :: IndexedOptic (Forget r) i s t a b -> (i -> a -> r) -> s -> r
ifoldMapOf o f = runForget $ o $ Forget (uncurry f)

{-
reindexed' :: Profunctor p => (j -> i) -> (i -> j) -> Iso (Ix p i a b) (Ix p i s t) (Ix p j a b) (Ix p j s t)

foo = reindexed' fromInteger toInteger
itoListOf (itrav1 . reindex id . itrav1) ["foo", "bar"]
itoListOf (itrav1 . (reix fromIntegral itrav2)) ["foo", "bar"]

itrav1 :: Ixtraversal Int [a] [b] a b
itrav1 = itraversed @Int

itrav2 :: Ixtraversal Integer [a] [b] a b
itrav2 = itraversed @Integer
itrav1 
itoListOf itraversed "foobar"
[(0,'f'),(1,'o'),(2,'o'),(3,'b'),(4,'a'),(5,'r')]

itoListOf (itraversed . itraversed) ["foo", "bar"]
[(0,'f'),(1,'o'),(2,'o'),(0,'b'),(1,'a'),(2,'r')]

itoListOf (itraversed . reix (+1) (itraversed @Int)) ["foo", "bar"]
[(1,'f'),(2,'o'),(3,'o'),(1,'b'),(2,'a'),(3,'r')]

itoListOf (itraversed' @Int) "foobar"
[(0,'f'),(0,'o'),(0,'o'),(0,'b'),(0,'a'),(0,'r')] --rings is in scope

itoListOf (itraversed . itraversed') ["foo", "bar"]
[(0,'f'),(0,'o'),(0,'o'),(0,'b'),(0,'a'),(0,'r')] -- ideally want 000111 here instead but can live w this

itoListOf (itraversed' . itraversed) ["foo", "bar"]
[(0,'f'),(1,'o'),(2,'o'),(0,'b'),(1,'a'),(2,'r')] 

-}



itoListOf :: Monoid i => IndexedOptic (Forget [(i, a)]) i s s a a -> s -> [(i, a)]
itoListOf o = (runForget $ o $ Forget (:[])) . (mempty,)


itraverseList :: Num n => Applicative f => (n -> a -> f b) -> [a] -> f [b]
itraverseList f = go 0
  where
    go _ []     = pure []
    go i (a:as) = (:) <$> f i a <*> go (i Prelude.+ 1) as

itraversedList :: Num n => Ixtraversal n [a] [b] a b
itraversedList = itraversing itraverseList



{-
--in Data.Map.Optic
itraversed :: IndexedOptic p i (Map i a) (Map i b) a b
itraversed = itraversing Map.traverseWithKey

positions :: Traversal s t a b -> Ixtraversal Int s t a b
positions tr =
  itraversing $ \f s ->
    flip evalState 0 $ blank $ flip blank s $ tr $ Star $ \a ->
      Compose $ (f <$> get <*> pure a) <* modify (+ 1)

-}







jcotraversed :: Distributive f => CoindexedOptic p j (f a) (f b) a b
jcotraversed = undefined



--newtype Jx j p s t = Jx (p s (j -> t))



ireturn :: Profunctor p => Optic p s t a b -> IndexedOptic p i s t a b
ireturn = undefined 

unindex :: Profunctor p => IndexedOptic p i s t a b -> Optic p s t a b
unindex o = undefined -- o . dimap snd id

asindex :: Profunctor p => IndexedOptic p i s t a b -> Optic p s t i b
asindex o = undefined -- o . dimap fst id

jreturn :: Profunctor p => p a b -> Jx p j a b
jreturn = rmap const

jjoin :: Strong p => Jx p a a b -> p a b
jjoin = peval

coindexed :: Strong p => Iso (Jx p s s t) (Jx p j a b) (p s t) (p a b)
coindexed = dimap jjoin jreturn

--jdimap :: Profunctor p => Profunctor q => (a -> b) -> (c -> d) -> p b (q b c) -> p a (q a d)
--jdimap l r = dimap l (dimap l r)

jdimap :: Profunctor p => (c -> a) -> (b -> d) -> Jx p j a b -> Jx p j c d
jdimap l r = dimap l (fmap r)

-- | 'Jx'' is freely strong.
--
-- See <https://r6research.livejournal.com/27858.html>.
--
jfirst' :: Profunctor p => Jx' p a b -> Jx' p (a, c) (b, c)
jfirst' = dimap fst (B.first @(,))
{-# INLINE jfirst' #-}





--jleft :: Cochoice p => Jx p j (a + c) (b + c) -> Jx p j a b
--jleft = dimap Left unleft . rmap (. Left)

--dimap (B.first @(+)) Left 

--jleft :: Closed p => Jx p j a b -> Jx p j (a + c) (b + c) 
--jleft = rmap (unleft . undefined) . curry'

junit :: Strong p => Jx' p :-> p
junit p = dimap fork apply (first' p)

jpastro :: Profunctor p => Iso (Jx' p a b) (Jx' p c d) (Pastro p a b) (Pastro p c d)
jpastro = dimap (\p -> Pastro apply p fork) (\(Pastro l m r) -> dimap (fst . r) (\y a -> l (y, (snd (r a)))) m)



--dimap (uncurry sta) (id ||| const bt) . right'
{-
ileft :: Ixprism i (a + c) (b + c) a b
ileft p = lmap assocl' (left' p)

(p a b -> p s t) -> p (i,a) b -> p (i,s) t

-- | Build an indexed lens from a getter and a setter.
--
-- If you want to build an 'IxLens' from the van Laarhoven representation, use
-- 'ilensVL'.
ilens :: (s -> (i , a)) -> (s -> b -> t) -> Ixlens i s t a b
ilens get set = ilensVl $ \f s -> set s <$> uncurry f (get s)
{-# INLINE ilens #-}

ilensVl :: (forall f. Functor f => (i -> a -> f b) -> s -> f t) -> Ixlens i s t a b
igrateVl :: (forall f. Functor f => (i -> f a -> b) -> f s -> t) -> Ixgrate i s t a b
itraversing0 :: (forall f. Functor f => (forall r. r -> f r) -> (i -> a -> f b) -> s -> f t) -> Ixtraversal0 i s t a b

ifirst :: Ixlens i i (a , c) (b , c) a b
ifirst = runIx . first' . Ix



-}

--type IndexedOptic p i s t a b = p (i , a) b -> p (i , s) t

--deltaIxed
--deltaJx
reindexed' :: Profunctor p => (j -> i) -> (i -> j) -> Iso (Ix p i a b) (Ix p i s t) (Ix p j a b) (Ix p j s t)
reindexed' ji ij = iso (reindex ji) (reindex ij)

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


{-

newtype Coindex p i a b = Coindex { runCoindex :: p a (i + b) }
newtype Ix p i a b = Ix { runIx :: p a (i -> b) }

instance Profunctor p => Profunctor (Ix p i) where
  dimap f g (Ix p) = Ix (dimap f (g .) p)

instance Strong p => Strong (Ix p i) where
  first' (Ix p) = Ix (rmap assocr' (first' p))

--apply
assocr' :: (a -> b, c) -> a -> (b, c)
assocr' (ab, c) = (,c) . ab

instance Choice p => Choice (Ix p i) where
  left' (Ix p) = Ix $ rmap eassocr' (left' p)

--eapply
eassocr' :: (a -> b) + c -> a -> b + c
eassocr' abc a = either (\ab -> Left $ ab a) Right abc

-- | TODO: Document
--
closed' :: Corepn (c -> a) (c -> b) a b
closed' = colift cotraverse

foo :: Strong p => Sieve p f => p a (i -> b) -> a -> i -> f b
foo = curry . sieve . uncurry'

instance (Strong p, Sieve p f) => Sieve (Ix p i) (Compose ((->) i) f) where
  sieve p a = Compose $ foo (runIx p) a

instance Representable (Ix (Forget r) i) where
  type Rep (Ix (Forget r) i) = Compose ((->) i) (Rep (Forget r)) 
  tabulate aifb = Ix . tabulate . forever $ getCompose . aifb


-}



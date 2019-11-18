{-# LANGUAGE UndecidableInstances #-}
{-# Language FunctionalDependencies #-}
{-# Language AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveGeneric         #-}

module Data.Profunctor.Optic.Indexed where

import Data.Profunctor.Traversing
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Iso
--import Data.Profunctor.Optic.Lens
import Data.Profunctor.Optic.Prism
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

import GHC.Generics (Generic)

{-
itraversed :: (TraversableWithIndex i t) => IxOptic p r (i -> r) (t a) (t b) a b
itraversed = undefined

itraversed' :: (TraversableWithIndex i t) => IxOptic p i (i -> j) (t a) (t b) a b
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

type IxOptic p i o s t a b = p i a b -> p o s t
--type IxOptic p i o s t a b = p (a , i) b -> p (s , o) t
--type IxOptic' p i o s a = IxOptic p i (o -> i) s s a a

--type IxOptic p i o s t a b = p a (i -> b) -> p s (o -> t)

itraversed' :: (TraversableWithIndex i t) => IxOptic p i (i -> j) (t a) (t b) a b
itraversed' = undefined

M.traverseWithKey :: Applicative t => (k -> a -> t b) -> Map k a -> t (Map k b)
traversal :: Traversable f => (s -> f a) -> (s -> f b -> t) -> Traversal s t a b

itraversing M.traverseWithKey
  :: (Choice p, Applicative (Rep p), Representable p) =>
     IxOptic p i (Map i a) (Map i b) a b
-}


--itraversing :: (forall f. Applicative f => (i -> a -> f b) -> s -> f t) -> IxTraversal i s t a b
--itraversing itr = traversing (\f s -> itr (curry f) s)
-- | A wrapper for a mapping or traversal function which uses an index.
--
-- For example, using the @containers@ library:
--
-- @
--  index mapWithKey
--    :: Indexed (a -> b) (Map i a -> Map i b) i
--  index foldMapWithKey
--    :: Monoid m => Indexed (a -> m) (Map i a -> m) i
--  index traverseWithKey
--    :: Applicative t => Indexed (a -> t b) (Map i a -> t (Map i b)) i
-- @
--
index :: ((i -> a) -> b) -> Indexed a b i
index = Indexed

-- | Lift a regular function into an indexed function.
--
-- For example, to traverse two layers, keeping only the first index:
--
-- @
--  index 'Data.Map.mapWithKey' % noindex 'Data.Map.map'
--    :: Monoid i =>
--       Indexed (a -> b) (Map i (Map k a) -> Map i (Map k b)) i
-- @
--
noindex :: Monoid i => (a -> b) -> Indexed a b i
noindex f = Indexed $ \a -> f (a mempty)

-- | Lift a particular index value into an 'Indexed'.
--
anindex :: i -> Indexed a a i
anindex i = Indexed ($i)

-- | The identity 'Indexed' for a 'Monoid' /i/.
--
idx :: Monoid i => Indexed a a i
idx = anindex mempty
{-
λ> :t zipWithOf indexed (,)
zipWithOf indexed (,) :: s -> s -> Indexed a (a, a) s
indexed :: Grate i (Indexed a b i) a b
indexed = grate index
-}


infixr 9 %
-- | Compose two 'Indexed's.
--
-- When /i/ is a 'Monoid', 'Indexed' can be used to compose indexed traversals, folds,
-- and setters.
--
-- For example, to keep track of only the first index seen, use @Data.Monoid.First@:
--
-- @
--  fmap (First . pure)
--    :: Indexed a b i -> Indexed a b (First i)
-- @
--
-- or keep track of all indices using a list
--
-- @
--  fmap (: [])
--    :: Indexed a b i -> Indexed a b [i]
-- @
--
-- @
--  index 'Data.Map.mapWithKey' % index 'Data.Map.mapWithKey'
--    :: Monoid i =>
--       Indexed (a -> b) (Map i (Map i a) -> Map i (Map i b)) i
-- @
--
-- and then applied using 'runIndexed':
--
-- @
--  runIndexed $ index 'Data.Map.mapWithKey' % index 'Data.Map.mapWithKey'
--    :: Monoid i => (i -> a -> b) -> Map i (Map i a) -> Map i (Map i b)
-- @
--
(%) :: Semigroup i => Indexed b c i -> Indexed a b i -> Indexed a c i
Indexed f % Indexed g = Indexed $ \b -> f $ \i1 -> g $ \i2 -> b (i1 <> i2)






-- | Class for 'Functor's that have an additional read-only index available.
class Functor f => FunctorWithIndex i f | f -> i where
  imap :: (i -> a -> b) -> f a -> f b


-- | Class for 'Foldable's that have an additional read-only index available.
class (FunctorWithIndex i f, Foldable f
      ) => FoldableWithIndex i f | f -> i where
  ifoldMap :: Monoid m => (i -> a -> m) -> f a -> m


  ifoldr :: (i -> a -> b -> b) -> b -> f a -> b
  ifoldr iabb b0 = (\e -> appEndo e b0) . ifoldMap (\i -> Endo #. iabb i)
  {-# INLINE ifoldr #-}

  ifoldl' :: (i -> b -> a -> b) -> b -> f a -> b
  ifoldl' ibab b0 s = ifoldr (\i a bb b -> bb $! ibab i b a) id s b0
  {-# INLINE ifoldl' #-}

-- | Class for 'Traversable's that have an additional read-only index available.
class (FoldableWithIndex i t, Traversable t
      ) => TraversableWithIndex i t | t -> i where
  itraverse :: Applicative f => (i -> a -> f b) -> t a -> f (t b)


instance FunctorWithIndex () Identity where
  imap f (Identity a) = Identity (f () a)
  {-# INLINE imap #-}

instance FoldableWithIndex () Identity where
  ifoldMap f (Identity a) = f () a
  {-# INLINE ifoldMap #-}

instance TraversableWithIndex () Identity where
  itraverse f (Identity a) = Identity <$> f () a
  {-# INLINE itraverse #-}

-- (,) k

instance FunctorWithIndex k ((,) k) where
  imap f (k, a) = (k, f k a)
  {-# INLINE imap #-}

instance FoldableWithIndex k ((,) k) where
  ifoldMap = uncurry
  {-# INLINE ifoldMap #-}

instance TraversableWithIndex k ((,) k) where
  itraverse f (k, a) = (,) k <$> f k a
  {-# INLINE itraverse #-}

-- (->) r

instance FunctorWithIndex r ((->) r) where
  imap f g x = f x (g x)
  {-# INLINE imap #-}

-- []

{-
instance FunctorWithIndex Int []
instance FoldableWithIndex Int []
instance TraversableWithIndex Int [] where
  -- Faster than @indexing traverse@, also best for folds and setters.
  itraverse f = traverse (uncurry f) . Prelude.zip [0..]
  {-# INLINE itraverse #-}
-}

-- Maybe

instance FunctorWithIndex () Maybe where
  imap f = fmap (f ())
  {-# INLINE imap #-}
instance FoldableWithIndex () Maybe where
  ifoldMap f = foldMap (f ())
  {-# INLINE ifoldMap #-}
instance TraversableWithIndex () Maybe where
  itraverse f = traverse (f ())
  {-# INLINE itraverse #-}

{-
-- | Traverse 'FoldableWithIndex' ignoring the results.
itraverse_ :: (FoldableWithIndex i t, Applicative f) => (i -> a -> f b) -> t a -> f ()
itraverse_ f = undefined --runTraversed . ifoldMap (\i -> Traversed #. f i)
{-# INLINE itraverse_ #-}

-- | Flipped 'itraverse_'.
ifor_ :: (FoldableWithIndex i t, Applicative f) => t a -> (i -> a -> f b) -> f ()
ifor_ = flip itraverse_
{-# INLINE ifor_ #-}
-}


newtype E a b = E { getE :: Either a b }

instance Semigroup r => Semigroup (E a r) where
    (<>) x@(E (Left _)) _ = x
    (<>) _ x@(E (Left _)) = x
    (<>) (E (Right a)) (E (Right b)) = E (Right ((<>) a b))

instance Monoid r => Monoid (E a r) where
    mempty = E (Right mempty)
    mappend = (<>)

type IxOpticJ p i j k l s t a b =
    p i j a b -> p k l s t
--one index pair for the contravariant argument (as previously), and one more pair for covariant.

--Writing operations using this encoding isn't different than previously. We make some concrete profunctor, use optic to transform it, and then use the result:

ifoldMapOfJ :: IxOpticJ (IxForgetJ r) (i, ()) () () k s t a b
            -> (i -> a -> r) -> s -> Either k r
ifoldMapOfJ o f =
    runIxForgetJ (o (IxForgetJ $ \(i, ()) -> Right . f i)) ()

newtype IxForgetJ r i j a b =
    IxForgetJ { runIxForgetJ :: i -> a -> Either j r }

instance Profunctor (IxForgetJ r i j) where
    dimap f _ (IxForgetJ p) =
        IxForgetJ (\i  -> p i . f)

instance Strong (IxForgetJ r i j) where
    first' (IxForgetJ p) =
        IxForgetJ (\i -> p i . fst)

instance Monoid r => Choice (IxForgetJ r i j) where
    right' (IxForgetJ p) =
        IxForgetJ (\i -> either (const (Right mempty)) (p i))

instance Monoid r => Traversing (IxForgetJ r i j) where
    wander f (IxForgetJ p)  = IxForgetJ $ \i ->
        getE . getConst . f (Const . E . p i)


---------------------------------------------------------------------
-- 'Ix'
---------------------------------------------------------------------




--http://hackage.haskell.org/package/indextype-0.3.0.1/docs/Control-IndexT.html
--http://hackage.haskell.org/package/with-index-0.1.0.0/docs/Data-WithIndex.html
--type IxOptic p i o s t a b = p i a b -> p o s t
--type IxOptic p i o s t a b = p (a , i) b -> p (s , o) t
--type IxOptic' p i o s a = IxOptic p i (o -> i) s s a a

--type IxOptic p i o s t a b = p a (i -> b) -> p s (o -> t)

{-
type IxOptic p i o s t a b = p (i , a) b -> p s t

type Ixlens i o s t a b = forall p. IxlensLike p i o s t a b
type IxlensLike p i o s t a b = Strong p => IxOptic p i o s t a b

type IxRepnLike p i o s t a b = Representable p => IxOptic p i o s t a b
type IxTraversal i o s t a b = forall p. Choice p => Applicative (Rep p) => IxRepnLike p i o s t a b
-}
type IxOptic p i s t a b = p (i , a) b -> p s t

type IxRepnLike p i s t a b = Representable p => IxOptic p i s t a b
type IxTraversal i s t a b = forall p. Choice p => Applicative (Rep p) => IxRepnLike p i s t a b


itraversing :: (forall f. Applicative f => (i -> a -> f b) -> s -> f t) -> IxTraversal i s t a b
itraversing itr = traversing (\f s -> itr (curry f) s)

itraversed :: TraversableWithIndex i t => IxTraversal i (t a) (t b) a b
itraversed = itraversing itraverse


--ifirst . closed :: (Strong p, Closed p) => p a b -> p (i -> a, c) (i -> (b, c))

newtype Ix p i a b = Ix { runIx :: p (i , a) b }

instance Profunctor p => Profunctor (Ix p i) where
  dimap f g (Ix p) = Ix (dimap (fmap f) g p)

instance Strong p => Strong (Ix p i) where
  first' (Ix p) = Ix $ lmap assocl (first' p)

instance Choice p => Choice (Ix p i) where
  left' (Ix p) = Ix $ lmap distl (left' p)

instance Sieve p f => Sieve (Ix p i) (Star f i) where
  sieve p a = Star $ (flip . curry . sieve $ runIx p) a

instance Representable p => Representable (Ix p i) where
  type Rep (Ix p i) = (Star (Rep p) i)
  tabulate aifb = Ix . tabulate . uncurry . flip $ runStar . aifb

--distl :: (a , b + c) -> (a , b) + c
--distl = fchoice --eswp . traverse eswp

--distr :: (a + b , c) -> a + (b , c)
--distr (f, b) = fmap (,b) f

{-
ilinear :: (forall f. Functor f => (i -> a -> f b) -> s -> f t) -> p j a b -> p (i -> j) s t
ivisit :: (forall f. Functor f => (forall r. r -> f r) -> (i -> a -> f b) -> s -> f t) -> p j a b -> p (i -> j) s t
iwander :: (forall f. Applicative f => (i -> a -> f b) -> s -> f t) -> p j a b -> p (i -> j) s t

ifirst :: Ixlens i i (a , c) (b , c) a b
ifirst = runIx . first' . Ix

newtype Coindexed p i a b = Coindexed { runCoindexed :: p a (i + b) }
newtype Ix p i a b = Ix { runIx :: p a (i -> b) }

instance Profunctor p => Profunctor (Ix p i) where
  dimap f g (Ix p) = Ix (dimap f (g .) p)

instance Strong p => Strong (Ix p i) where
  first' (Ix p) = Ix (rmap distr (first' p))

--apply
distr :: (a -> b, c) -> a -> (b, c)
distr (ab, c) = (,c) . ab

instance Choice p => Choice (Ix p i) where
  left' (Ix p) = Ix $ rmap edistr (left' p)

--eapply
edistr :: (a -> b) + c -> a -> b + c
edistr abc a = either (\ab -> Left $ ab a) Right abc

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


{-
bar :: (d -> i -> Const r c) -> d -> Const r (i -> c)
bar f d =  

instance Representable p => Representable (Ix p i) where
  type Rep (Ix p i) = Compose ((->) i) (Rep p) 
  tabulate aifb = Ix . tabulate . bar $ getCompose . aifb

bar :: Functor f => (d -> i -> f c) -> d -> f (i -> c)
bar f d = distribute (Compose $ f d)

-}

{-
instance Sieve p f => Sieve (Ix p i) (Compose f ((->) i)) where
  sieve p a = Compose $ sieve (runIx p) a

instance Representable p => Representable (Ix p i) where
  type Rep (Ix p i) = Compose (Rep p) ((->) i) 
  tabulate aifb = Ix . tabulate $ getCompose . aifb

bar :: Distributive f => (d -> i -> f c) -> d -> f (i -> c)
bar f d = distribute (f d)

instance Cosieve p f => Cosieve (Ix p i) (Compose f ((->) i)) where
  --cosieve p a = Compose $ sieve (runIx p) a
  cosieve p (Compose f) = (undefined . cosieve $ runIx p) f
-}


{-
foo :: (i -> a -> f b) -> a -> Compose f ((->) i) b
foo iab a = Compose $ flip iab a

itraversing :: (forall f. Applicative f => (i -> a -> f b) -> o -> s -> f t) -> IxTraversal i o s t a b
itraversing abst = runIx . tabulate . foo . abst . undefined . sieve . Ix


foo :: (i -> a -> f b) -> a -> Compose f ((->) i) b
foo iab = Compose $ iab a

bar :: (a -> Compose f ((->) i) b) -> i -> a -> f b
bar aib i a =  getCompose (aib a) i

itraversing :: (forall f. Applicative f => (i -> a -> f b) -> o -> s -> f t) -> IxTraversal i o s t a b
itraversing abst = runIx . tabulate . (Compose .) . abst . (. getCompose) . sieve . Ix

itraversing abst = runIx . lift ((Compose .) . abst . (. getCompose)) . Ix

itraversing abst = runIx . tabulate . (Compose .) . abst . (. getCompose) . sieve . Ix

instance (Representable p, Contravariant (Rep p)) => Representable (Ix p i) where
  type Rep (Ix p i) = (Star (Rep p) i)
  tabulate aifb = Ix . bip $ runStar . aifb

--tabulate . uncurry
bip :: Representable p => (d -> i -> Rep p c) -> p d (i -> c)
bip f = tabulate . swap f
-}

{-
instance Representable (Ix (Forget r) i) where
  type Rep (Ix (Forget r) i) = (Star (Rep (Forget r)) i)
  tabulate aifb = _ $ runStar . aifb
--Ix . undefined . tabulate . undefined

bip :: (d -> i -> Const r c) -> Ix (Forget r) i d c
bip f = 
-}

{-
instance (Strong p, Sieve p f) => Sieve (Ix p i) (Star f i) where
  sieve p a = Star $ (curry . sieve . uncurry' $ runIx p) a

-- TODO: don't try to do this polymophically. specialize to Star etc?
instance (Closed p, Representable p) => Representable (Ix p i) where
  type Rep (Ix p i) = (Star (Rep p) i)
  tabulate aifb = Ix . curry' . tabulate . uncurry $ runStar . aifb

curry' . cotabulate
  :: (Closed p, Corepresentable p) =>
     (Corep p (a, b) -> c) -> p a (b -> c)

--ifoldMapOf :: Monoid r => AFold r s a -> (a -> r) -> s -> r
--ifoldMapOf o = (getConst #.) #. runStar #. o .# Star .# (Const #.)
--ifoldMapOf o f = getConst . runStar (o (Ix (Star $ Const (uncurry f))))
--itraverseOf o = runStar #. runIx #. o .# Ix .# Star

--itoListOf :: IxOptic (Forget [(i, a)]) i j s s a a -> s -> [(i, a)]
--itoListOf o = runForget (runIx (o (Ix (Forget (:[])))))

--itoListOf :: Closed (Forget [(a1, b1)]) => (Forget [(a1, b1)] a1 (b1 -> c) -> Forget r a2 b2) -> a2 -> r
--itoListOf o = runForget (o (curry' (Forget (:[]))))

--itraversed :: (TraversableWithIndex i t) => IxOptic p i  (t a) (t b) a b
--itraversed = undefined
itraversed :: TraversableWithIndex i t => IxTraversal i o (t a) (t b) a b
itraversed = itraversing $ \f _ s -> itraverse f s

foo :: (i -> a -> f b) -> a -> Star f i b
foo iab a = Star $ flip iab a

bar :: (a -> Star f i b) -> i -> a -> f b
bar aib i a =  runStar (aib a) i

itraversing :: (forall f. Applicative f => (i -> a -> f b) -> o -> s -> f t) -> IxTraversal i o s t a b
itraversing abst = runIx . tabulate . foo . abst . bar . sieve . Ix

itraverseList :: Applicative f => (Int -> a -> f b) -> [a] -> f [b]
itraverseList f = go 0
  where
    go _ []     = pure []
    go i (a:as) = (:) <$> f i a <*> go (i Prelude.+ 1) as

itraversedList :: IxTraversal Int (o -> Int) [a] [b] a b
itraversedList = itraversing  $ \f _ s -> itraverseList f s
-}
--ifoldMapOfC o f = runIxForget (o (IxForget f)) id

--itraverse :: Applicative f => (i -> a -> f b) -> t a -> f (t b)

--itraversing :: (forall f. Applicative f => (a -> f b) -> s -> f t) -> Traversal s t a b
--itraversing :: (Representable p, f ~ Rep p) => ((a1 -> Star f i1 b1) -> a2 -> Star f i2 b2) -> IxOptic p i1 i2 a2 b2 a1 b1
--itraversing abst = runIx . tabulate . abst . sieve . Ix


{-

indexed = dimap runIx Ix

runStar . runIx . ixfirst . Ix . Star

--
traversing :: (forall f. Applicative f => (a -> f b) -> s -> f t) -> Traversal s t a b
traversing abst = tabulate . abst . sieve

traverseOf :: Applicative f => ATraversal f s t a b -> (a -> f b) -> s -> f t
traverseOf o = runStar #. o .# Star


itraversing
  :: (Distributive (Rep p1), Representable p1, Traversable (Rep p1),
      Traversable f, Sieve p2 f) =>
     ((a1 -> Star (Compose (Either j1) f) i1 b1)
      -> a2 -> Star (Compose (Either j2) (Rep p1)) i2 b2)
     -> p2 (i1, a1) (j1 + b1) -> p1 (i2, a2) (j2 + b2)


instance Traversing p => Traversing (Ix p i) where
    lift f (Ix p) = Ix $
         lift (\g (i, s) -> f (curry g i) s) p

instance Closed (Ix (->) i) where
  closed (Ix iab) = Ix $ \i xa x -> iab i (xa x)


instance Costrong (Ix (->) i) where
  unfirst (Ix iadbd) = Ix $ \i a -> let
      (b, d) = iadbd i (a, d)
    in b

instance Cosieve (Ix (->) i) ((,) i) where
  cosieve = runIx
  {-# INLINE cosieve #-}

instance Corepresentable (Ix (->) i) where
  type Corep (Ix i) = (,) i
  cotabulate = Ix
  {-# INLINE cotabulate #-}


instance Representable (Ix (->) i) where
  type Rep (Ix i) = (->) i
  tabulate = Ix . uncurry . flip
  {-# INLINE tabulate #-}


-}


{-
-- | Needed for indexed traversals.
newtype IxStar f i a b = IxStar { runIxStar :: i -> a -> f b }

-- | Needed for indexed folds.
newtype IxForget r i a b = IxForget { runIxForget :: i -> a -> r }

instance Profunctor (IxForget r i) where
    dimap f _ (IxForget p) = IxForget (\i -> p i . f)

instance Strong (IxForget r i) where
    first' (IxForget p) = IxForget (\i -> p i . fst)

instance Monoid r => Choice (IxForget r i) where
    right' (IxForget p) =  IxForget (\i -> either (const mempty) (p i))

instance Monoid r => Traversing (IxForget r i) where
    wander f (IxForget p) = IxForget (\i -> getConst . f (Const . p i))

itoListOfC :: IxOptic' (IxForget [(i, a)]) i (i -> i) s a -> s -> [(i, a)]
itoListOfC o = ifoldMapOfC o (\i a -> [(i, a)])

ifoldMapOfC :: IxOptic' (IxForget r) i (i -> i) s a -> (i -> a -> r) -> s -> r
ifoldMapOfC o f = runIxForget (o (IxForget f)) id

ifoldMapOfC2 :: IxOptic' (IxForget r) k (i -> j -> k) s a -> (i -> j -> k) -> (k -> a -> r) -> s -> r
ifoldMapOfC2 o ijk f = runIxForget (o (IxForget f)) ijk

ifoldMapOfC2' :: IxOptic' (IxForget r) (a -> r) (i -> j -> a -> r) s a -> (i -> j -> a -> r) -> s -> r
ifoldMapOfC2' o f = runIxForget (o (IxForget id)) f

-}



{-


instance Functor (Ix (->) i a) where
  fmap g (Ix f) = Ix $ \i a -> g (f i a)
  {-# INLINE fmap #-}

instance Apply (Ix (->) i a) where
  Ix f <.> Ix g = Ix $ \i a -> f i a (g i a)
  {-# INLINE (<.>) #-}

instance Applicative (Ix (->) i a) where
  pure b = Ix $ \_ _ -> b
  {-# INLINE pure #-}
  Ix f <*> Ix g = Ix $ \i a -> f i a (g i a)
  {-# INLINE (<*>) #-}

instance Bind (Ix (->) i a) where
  Ix f >>- k = Ix $ \i a -> runIx (k (f i a)) i a
  {-# INLINE (>>-) #-}

instance Monad (Ix (->) i a) where
  return = pure
  {-# INLINE return #-}
  Ix f >>= k = Ix $ \i a -> runIx (k (f i a)) i a
  {-# INLINE (>>=) #-}

instance MonadFix (Ix (->) i a) where
  mfix f = Ix $ \ i a -> let o = runIx (f o) i a in o
  {-# INLINE mfix #-}

instance Category (Ix (->) i) where
  id = Ix (const id)
  {-# INLINE id #-}
  Ix f . Ix g = Ix $ \i -> f i . g i
  {-# INLINE (.) #-}

instance Arrow (Ix (->) i) where
  arr f = Ix (\_ -> f)
  {-# INLINE arr #-}
  first f = Ix (Arrow.first . runIx f)
  {-# INLINE first #-}
  second f = Ix (Arrow.second . runIx f)
  {-# INLINE second #-}
  Ix f *** Ix g = Ix $ \i -> f i *** g i
  {-# INLINE (***) #-}
  Ix f &&& Ix g = Ix $ \i -> f i &&& g i
  {-# INLINE (&&&) #-}

instance ArrowChoice (Ix (->) i) where
  left f = Ix (left . runIx f)
  {-# INLINE left #-}
  right f = Ix (right . runIx f)
  {-# INLINE right #-}
  Ix f +++ Ix g = Ix $ \i -> f i +++ g i
  {-# INLINE (+++)  #-}
  Ix f ||| Ix g = Ix $ \i -> f i ||| g i
  {-# INLINE (|||) #-}

instance ArrowApply (Ix (->) i) where
  app = Ix $ \ i (f, b) -> runIx f i b
  {-# INLINE app #-}

instance ArrowLoop (Ix (->) i) where
  loop (Ix f) = Ix $ \i b -> let (c,d) = f i (b, d) in c
  {-# INLINE loop #-}

instance Conjoined (Ix (->) i) where
  distrib (Ix iab) = Ix $ \i fa -> iab i <$> fa
  {-# INLINE distrib #-}

instance i ~ j => Indexable i (Ix (->) j) where
  indexed = runIx
  {-# INLINE indexed #-}

-}

{-# LANGUAGE TupleSections #-}
{-# LANGUAGE  TypeFamilies #-}

module Data.Profunctor.Optic.Type.Indexed where

import Data.Profunctor.Rep
import Data.Profunctor.Sieve
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Type.Class 
import Data.Profunctor.Optic.Prelude

---------------------------------------------------------------------
--
---------------------------------------------------------------------


{-
For the case of 'h = (,)', these are Kleisli arrows built from the state monad, i.e. 
functions of type a -> s -> (b, s) where s is our state. 
We can write these more symmetrically as functions of type (a, s) -> (b, s)
-}


newtype Hughes h s t a b = Hughes { runHughes :: h a s -> h b t }
type Circuit s t a b = Hughes (,) s t a b

invert :: Swap h => Hughes h s t a b -> Hughes h a b s t
invert (Hughes h) = Hughes $ swap . h . swap

instance Bifunctor h => Profunctor (Hughes h s t) where
  dimap f g (Hughes h) = Hughes $ first g . h . first f

---------------------------------------------------------------------
--
---------------------------------------------------------------------

---------------------------------------------------------------------
-- 
---------------------------------------------------------------------

newtype Indexed p i a b = Indexed { runIndexed :: p (i, a) b }

type IOptic p i s t a b = Indexed p i a b -> p s t
type IOptic' p i s a = IOptic p i s s a a

instance Profunctor p => Profunctor (Indexed p i) where
    dimap f g (Indexed p) = Indexed (dimap (fmap f) g p)
    --dimap f g (Indexed p) = Indexed (dimap (second' f) g p)

instance Strong p => Strong (Indexed p i) where
    first' (Indexed p) = Indexed (lmap unassoc (first' p))

instance Choice p => Choice (Indexed p i) where
    left' (Indexed p) = Indexed $
        lmap (\(i, e) -> first (i,) e) (left' p)

instance Traversing p => Traversing (Indexed p i) where
    lift f (Indexed p) = Indexed $
         lift (\g (i, s) -> f (curry g i) s) p

instance Traversing1 p => Traversing1 (Indexed p i) where
    over1 f (Indexed p) = Indexed $
         over1 (\g (i, s) -> f (curry g i) s) p

{-
instance Closed (Indexed (->) i) where
  closed (Indexed iab) = Indexed $ \i xa x -> iab i (xa x)

instance Costrong (Indexed (->) i) where
  unfirst (Indexed iadbd) = Indexed $ \i a -> let
      (b, d) = iadbd i (a, d)
    in b

instance Representable (Indexed (->) i) where
  type Rep (Indexed i) = (->) i
  tabulate = Indexed . uncurry . flip
  {-# INLINE tabulate #-}

instance Corepresentable (Indexed (->) i) where
  type Corep (Indexed i) = (,) i
  cotabulate = Indexed
  {-# INLINE cotabulate #-}
-}



instance Sieve (Indexed (->) i) ((->) i) where
  sieve = flip . curry . runIndexed
  {-# INLINE sieve #-}

instance Cosieve (Indexed (->) i) ((,) i) where
  cosieve = runIndexed
  {-# INLINE cosieve #-}


itraversing 
  :: Traversing p
  => (forall f. Applicative f => (i -> a -> f b) -> s -> f t)
  -> IOptic p i s t a b
itraversing itr (Indexed pab) = lift (\f s -> itr (curry f) s) pab

--ifoldMapOf :: IOptic' (Star (Const r)) i s a -> (i -> a -> r) -> s -> r
--ifoldMapOf o f = h where Indexed h = o (Indexed $ Star . Const . uncurry f)
--ifoldMapOf = between (extract $ getConst) (insert $ Indexed . Const . uncurry)
--ifoldMapOf o f = getConst . runStar (o (Indexed (Star $ Const (uncurry f))))


--foldMapOf :: FoldLike r s a -> (a -> r) -> s -> r
--foldMapOf = between (extract getConst) (insert Const)


icompose 
  :: Profunctor p
  => (i -> j -> k)
  -> (Indexed p i u v -> p s t)
  -> (Indexed (Indexed p i) j a b -> Indexed p i u v)
  -> (Indexed p k a b -> p s t)
icompose ijk stuv uvab ab = icompose' ijk
    (stuv . Indexed)
    (runIndexed . uvab . Indexed . Indexed)
    (runIndexed ab)

icompose' 
  :: Profunctor p
  => (i -> j -> k)
  -> (p (i, u) v -> p s t)
  -> (p (i, (j, a)) b -> p (i, u) v)
  -> (p (k, a) b -> p s t)
icompose' ijk stuv uvab ab = stuv (uvab (lmap f ab))
  where
    f (i, (j, a)) = (ijk i j, a)

itraverseList :: Applicative f => (Int -> a -> f b) -> [a] -> f [b]
itraverseList f = go 0
  where
    go _ []     = pure []
    go i (a:as) = (:) <$> f i a <*> go (i + 1) as

itraversedList :: Traversing p => IOptic p Int [a] [b] a b
itraversedList = itraversing itraverseList

{-


instance Functor (Indexed (->) i a) where
  fmap g (Indexed f) = Indexed $ \i a -> g (f i a)
  {-# INLINE fmap #-}

instance Apply (Indexed (->) i a) where
  Indexed f <.> Indexed g = Indexed $ \i a -> f i a (g i a)
  {-# INLINE (<.>) #-}

instance Applicative (Indexed (->) i a) where
  pure b = Indexed $ \_ _ -> b
  {-# INLINE pure #-}
  Indexed f <*> Indexed g = Indexed $ \i a -> f i a (g i a)
  {-# INLINE (<*>) #-}

instance Bind (Indexed (->) i a) where
  Indexed f >>- k = Indexed $ \i a -> runIndexed (k (f i a)) i a
  {-# INLINE (>>-) #-}

instance Monad (Indexed (->) i a) where
  return = pure
  {-# INLINE return #-}
  Indexed f >>= k = Indexed $ \i a -> runIndexed (k (f i a)) i a
  {-# INLINE (>>=) #-}

instance MonadFix (Indexed (->) i a) where
  mfix f = Indexed $ \ i a -> let o = runIndexed (f o) i a in o
  {-# INLINE mfix #-}

instance Category (Indexed (->) i) where
  id = Indexed (const id)
  {-# INLINE id #-}
  Indexed f . Indexed g = Indexed $ \i -> f i . g i
  {-# INLINE (.) #-}

instance Arrow (Indexed (->) i) where
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

instance ArrowChoice (Indexed (->) i) where
  left f = Indexed (left . runIndexed f)
  {-# INLINE left #-}
  right f = Indexed (right . runIndexed f)
  {-# INLINE right #-}
  Indexed f +++ Indexed g = Indexed $ \i -> f i +++ g i
  {-# INLINE (+++)  #-}
  Indexed f ||| Indexed g = Indexed $ \i -> f i ||| g i
  {-# INLINE (|||) #-}

instance ArrowApply (Indexed (->) i) where
  app = Indexed $ \ i (f, b) -> runIndexed f i b
  {-# INLINE app #-}

instance ArrowLoop (Indexed (->) i) where
  loop (Indexed f) = Indexed $ \i b -> let (c,d) = f i (b, d) in c
  {-# INLINE loop #-}

instance Conjoined (Indexed (->) i) where
  distrib (Indexed iab) = Indexed $ \i fa -> iab i <$> fa
  {-# INLINE distrib #-}

instance i ~ j => Indexable i (Indexed (->) j) where
  indexed = runIndexed
  {-# INLINE indexed #-}


------------------------------------------------------------------------------
-- Hughes
------------------------------------------------------------------------------

-- | 'Applicative' composition of @'Control.Monad.Trans.State.Lazy.State' 'Int'@ with a 'Functor', used
-- by 'Control.Lens.Indexed.indexed'.
--
-- This is co-strong
-- λ> :t re first'
-- re first' :: Costrong p => Optic p b a (b, c) (a, c)
newtype Hughes f a = Hughes { runHughes :: Int -> (Int, f a) }

instance Functor f => Functor (Hughes f) where
  fmap f (Hughes m) = Hughes $ \i -> case m i of
    (j, x) -> (j, fmap f x)
  {-# INLINE fmap #-}

instance Apply f => Apply (Hughes f) where
  Hughes mf <.> Hughes ma = Hughes $ \i -> case mf i of
    (j, ff) -> case ma j of
       ~(k, fa) -> (k, ff <.> fa)
  {-# INLINE (<.>) #-}

instance Applicative f => Applicative (Hughes f) where
  pure x = Hughes $ \i -> (i, pure x)
  {-# INLINE pure #-}
  Hughes mf <*> Hughes ma = Hughes $ \i -> case mf i of
    (j, ff) -> case ma j of
       ~(k, fa) -> (k, ff <*> fa)
  {-# INLINE (<*>) #-}

instance Contravariant f => Contravariant (Hughes f) where
  contramap f (Hughes m) = Hughes $ \i -> case m i of
    (j, ff) -> (j, contramap f ff)
  {-# INLINE contramap #-}

instance Semi.Semigroup (f a) => Semi.Semigroup (Hughes f a) where
    Hughes mx <> Hughes my = Hughes $ \i -> case mx i of
      (j, x) -> case my j of
         ~(k, y) -> (k, x Semi.<> y)
    {-# INLINE (<>) #-}

-- |
--
-- >>> "cat" ^@.. (folded <> folded)
-- [(0,'c'),(1,'a'),(2,'t'),(0,'c'),(1,'a'),(2,'t')]
--
-- >>> "cat" ^@.. indexing (folded <> folded)
-- [(0,'c'),(1,'a'),(2,'t'),(3,'c'),(4,'a'),(5,'t')]
instance Monoid (f a) => Monoid (Hughes f a) where
    mempty = Hughes $ \i -> (i, mempty)
    {-# INLINE mempty #-}

    mappend (Hughes mx) (Hughes my) = Hughes $ \i -> case mx i of
      (j, x) -> case my j of
         ~(k, y) -> (k, mappend x y)
    {-# INLINE mappend #-}

-- | Transform a 'Control.Lens.Traversal.Traversal' into an 'Control.Lens.Traversal.IndexedTraversal' or
-- a 'Control.Lens.Fold.Fold' into an 'Control.Lens.Fold.IndexedFold', etc.
--
-- @
-- 'indexing' :: 'Control.Lens.Type.Traversal' s t a b -> 'Control.Lens.Type.IndexedTraversal' 'Int' s t a b
-- 'indexing' :: 'Control.Lens.Type.Prism' s t a b     -> 'Control.Lens.Type.IndexedTraversal' 'Int' s t a b
-- 'indexing' :: 'Control.Lens.Type.Lens' s t a b      -> 'Control.Lens.Type.IndexedLens' 'Int'  s t a b
-- 'indexing' :: 'Control.Lens.Type.Iso' s t a b       -> 'Control.Lens.Type.IndexedLens' 'Int' s t a b
-- 'indexing' :: 'Control.Lens.Type.Fold' s a          -> 'Control.Lens.Type.IndexedFold' 'Int' s a
-- 'indexing' :: 'Control.Lens.Type.View' s a        -> 'Control.Lens.Type.IndexedView' 'Int' s a
-- @
--
-- @'indexing' :: 'Indexable' 'Int' p => 'Control.Lens.Type.LensLike' ('Hughes' f) s t a b -> 'Control.Lens.Type.Over' p f s t a b@
indexing :: Indexable Int p => ((a -> Hughes f b) -> s -> Hughes f t) -> p a (f b) -> s -> f t
indexing l iafb s = snd $ runHughes (l (\a -> Hughes (\i -> i `seq` (i + 1, indexed iafb i a))) s) 0
{-# INLINE indexing #-}

------------------------------------------------------------------------------
-- Hughes64
------------------------------------------------------------------------------

-- | 'Applicative' composition of @'Control.Monad.Trans.State.Lazy.State' 'Int64'@ with a 'Functor', used
-- by 'Control.Lens.Indexed.indexed64'.
newtype Hughes64 f a = Hughes64 { runHughes64 :: Int64 -> (Int64, f a) }

instance Functor f => Functor (Hughes64 f) where
  fmap f (Hughes64 m) = Hughes64 $ \i -> case m i of
    (j, x) -> (j, fmap f x)
  {-# INLINE fmap #-}

instance Apply f => Apply (Hughes64 f) where
  Hughes64 mf <.> Hughes64 ma = Hughes64 $ \i -> case mf i of
    (j, ff) -> case ma j of
       ~(k, fa) -> (k, ff <.> fa)
  {-# INLINE (<.>) #-}

instance Applicative f => Applicative (Hughes64 f) where
  pure x = Hughes64 $ \i -> (i, pure x)
  {-# INLINE pure #-}
  Hughes64 mf <*> Hughes64 ma = Hughes64 $ \i -> case mf i of
    (j, ff) -> case ma j of
       ~(k, fa) -> (k, ff <*> fa)
  {-# INLINE (<*>) #-}

instance Contravariant f => Contravariant (Hughes64 f) where
  contramap f (Hughes64 m) = Hughes64 $ \i -> case m i of
    (j, ff) -> (j, contramap f ff)
  {-# INLINE contramap #-}

-- | Transform a 'Control.Lens.Traversal.Traversal' into an 'Control.Lens.Traversal.IndexedTraversal' or
-- a 'Control.Lens.Fold.Fold' into an 'Control.Lens.Fold.IndexedFold', etc.
--
-- This combinator is like 'indexing' except that it handles large traversals and folds gracefully.
--
-- @
-- 'indexing64' :: 'Control.Lens.Type.Traversal' s t a b -> 'Control.Lens.Type.IndexedTraversal' 'Int64' s t a b
-- 'indexing64' :: 'Control.Lens.Type.Prism' s t a b     -> 'Control.Lens.Type.IndexedTraversal' 'Int64' s t a b
-- 'indexing64' :: 'Control.Lens.Type.Lens' s t a b      -> 'Control.Lens.Type.IndexedLens' 'Int64' s t a b
-- 'indexing64' :: 'Control.Lens.Type.Iso' s t a b       -> 'Control.Lens.Type.IndexedLens' 'Int64' s t a b
-- 'indexing64' :: 'Control.Lens.Type.Fold' s a          -> 'Control.Lens.Type.IndexedFold' 'Int64' s a
-- 'indexing64' :: 'Control.Lens.Type.View' s a        -> 'Control.Lens.Type.IndexedView' 'Int64' s a
-- @
--
-- @'indexing64' :: 'Indexable' 'Int64' p => 'Control.Lens.Type.LensLike' ('Hughes64' f) s t a b -> 'Control.Lens.Type.Over' p f s t a b@
indexing64 :: Indexable Int64 p => ((a -> Hughes64 f b) -> s -> Hughes64 f t) -> p a (f b) -> s -> f t
indexing64 l iafb s = snd $ runHughes64 (l (\a -> Hughes64 (\i -> i `seq` (i + 1, indexed iafb i a))) s) 0
{-# INLINE indexing64 #-}

-}


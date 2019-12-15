{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Traversal (
    -- * Traversal & Ixtraversal
    Traversal
  , Traversal'
  , Ixtraversal
  , Ixtraversal'
  , traversing
  , itraversing
  , traversalVl
  , itraversalVl
  , noix
  , ix
    -- * Cotraversal & Cxtraversal
  , Cotraversal
  , Cotraversal'
  , cotraversal
  , cotraversing
  , cotraversalVl
    -- * Optics
  , traversed
  , itraversedRep
  , cotraversed
  , both
  , duplicated
  , bitraversed
    -- * Primitive operators
  , withTraversal
  , withCotraversal
  , withMealy
    -- * Operators
  , sequences
  , distributes 
    -- * Carriers
  , ATraversal
  , ATraversal'
  , ACotraversal
  , ACotraversal'
  , mealy
  , Mealy(..)
) where

import Control.Category
import Control.Arrow
import Data.Bitraversable
import Data.List.NonEmpty as NonEmpty
import Data.Profunctor.Optic.Grate
import Data.Profunctor.Optic.Lens
import Data.Profunctor.Optic.Import hiding (id,(.))
import Data.Profunctor.Optic.Types
import Data.Semigroupoid
import Data.Semiring
import Control.Monad.Trans.State
import Prelude (Foldable(..), reverse)
import qualified Data.Functor.Rep as F

import Control.Applicative
import Control.Comonad
import Control.Monad.Reader.Class
import Control.Monad.Fix
import Control.Monad.Zip
import Data.Distributive
import Data.Foldable
import Data.Profunctor.Closed
import Data.Profunctor
import Data.Profunctor.Sieve
import Data.Profunctor.Rep as Profunctor
import Data.Profunctor.Unsafe
import Unsafe.Coerce

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XFlexibleContexts
-- >>> :set -XTypeApplications
-- >>> :set -XTupleSections
-- >>> :set -XRankNTypes
-- >>> import Data.Maybe
-- >>> import Data.Int.Instance ()
-- >>> import Data.List.NonEmpty (NonEmpty(..))
-- >>> import qualified Data.List.NonEmpty as NE
-- >>> import Data.Functor.Identity
-- >>> import Data.List.Index
-- >>> :load Data.Profunctor.Optic
-- >>> let catchOn :: Int -> Cxprism' Int (Maybe String) String ; catchOn n = kjust $ \k -> if k==n then Just "caught" else Nothing
-- >>> let itraversed :: Ixtraversal Int [a] [b] a b ; itraversed = itraversalVl itraverse

---------------------------------------------------------------------
-- 'Traversal' & 'Ixtraversal'
---------------------------------------------------------------------

type ATraversal f s t a b = Applicative f => ARepn f s t a b

type ATraversal' f s a = ATraversal f s s a a

-- | Obtain a 'Traversal' by lifting a lens getter and setter into a 'Traversable' functor.
--
-- @
--  'withLens' o 'traversing' ≡ 'traversed' . o
-- @
--
-- Compare 'Data.Profunctor.Optic.Moore.folding'.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input functions constitute a legal lens:
--
-- * @sa (sbt s a) ≡ a@
--
-- * @sbt s (sa s) ≡ s@
--
-- * @sbt (sbt s a1) a2 ≡ sbt s a2@
--
-- See 'Data.Profunctor.Optic.Property'.
--
-- The resulting optic can detect copies of the lens stucture inside
-- any 'Traversable' container. For example:
--
-- >>> lists (traversing snd $ \(s,_) b -> (s,b)) [(0,'f'),(1,'o'),(2,'o'),(3,'b'),(4,'a'),(5,'r')]
-- "foobar"
--
traversing :: Traversable f => (s -> a) -> (s -> b -> t) -> Traversal (f s) (f t) a b
traversing sa sbt = repn traverse . lens sa sbt

-- | Obtain a 'Ixtraversal' by lifting an indexed lens getter and setter into a 'Traversable' functor.
--
-- @
--  'withIxlens' o 'itraversing' ≡ 'itraversed' . o
-- @
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input functions constitute a legal 
-- indexed lens:
--
-- * @snd . sia (sbt s a) ≡ a@
--
-- * @sbt s (snd $ sia s) ≡ s@
--
-- * @sbt (sbt s a1) a2 ≡ sbt s a2@
--
-- See 'Data.Profunctor.Optic.Property'.
--
itraversing :: Monoid i => Traversable f => (s -> (i , a)) -> (s -> b -> t) -> Ixtraversal i (f s) (f t) a b
itraversing sia sbt = repn (\iab -> traverse (curry iab mempty) . snd) . ilens sia sbt 

-- | Obtain a profunctor 'Traversal' from a Van Laarhoven 'Traversal'.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @abst pure ≡ pure@
--
-- * @fmap (abst f) . abst g ≡ getCompose . abst (Compose . fmap f . g)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
traversalVl :: (forall f. Applicative f => (a -> f b) -> s -> f t) -> Traversal s t a b
traversalVl abst = tabulate . abst . sieve

-- | Lift an indexed VL traversal into an indexed profunctor traversal.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @iabst (const pure) ≡ pure@
--
-- * @fmap (iabst $ const f) . (iabst $ const g) ≡ getCompose . iabst (const $ Compose . fmap f . g)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
itraversalVl :: (forall f. Applicative f => (i -> a -> f b) -> s -> f t) -> Ixtraversal i s t a b
itraversalVl f = traversalVl $ \iab -> f (curry iab) . snd

-- | Lift a VL traversal into an indexed profunctor traversal that ignores its input.
--
-- Useful as the first optic in a chain when no indexed equivalent is at hand.
--
-- >>> ilists (noix traversed . itraversed) ["foo", "bar"]
-- [(0,'f'),(1,'o'),(2,'o'),(0,'b'),(1,'a'),(2,'r')]
--
-- >>> ilists (itraversed . noix traversed) ["foo", "bar"]
-- [(0,'f'),(0,'o'),(0,'o'),(0,'b'),(0,'a'),(0,'r')]
--
noix :: Monoid i => Traversal s t a b -> Ixtraversal i s t a b
noix o = itraversalVl $ \iab s -> flip runStar s . o . Star $ iab mempty

-- | Index a traversal with a 'Data.Semiring'.
--
-- >>> ilists (ix traversed . ix traversed) ["foo", "bar"]
-- [((),'f'),((),'o'),((),'o'),((),'b'),((),'a'),((),'r')]
--
-- >>> ilists (ix @Int traversed . ix traversed) ["foo", "bar"]
-- [(0,'f'),(1,'o'),(2,'o'),(0,'b'),(1,'a'),(2,'r')]
--
-- >>> ilists (ix @[()] traversed . ix traversed) ["foo", "bar"]
-- [([],'f'),([()],'o'),([(),()],'o'),([],'b'),([()],'a'),([(),()],'r')]
--
-- >>> ilists (ix @[()] traversed % ix traversed) ["foo", "bar"]
-- [([],'f'),([()],'o'),([(),()],'o'),([()],'b'),([(),()],'a'),([(),(),()],'r')]
--
ix :: Monoid i => Semiring i => Traversal s t a b -> Ixtraversal i s t a b
ix o = itraversalVl $ \f s ->
  flip evalState mempty . getCompose . flip runStar s . o . Star $ \a ->
    Compose $ (f <$> get <*> pure a) <* modify (<> sunit) 

---------------------------------------------------------------------
-- 'Cotraversal' & 'Cxtraversal'
---------------------------------------------------------------------

type ACotraversal f s t a b = Comonad f => ACorepn f s t a b

type ACotraversal' f s a = ACotraversal f s s a a

-- | Obtain a 'Cotraversal' directly. 
--
cotraversal :: Distributive g => (g b -> s -> g a) -> (g b -> t) -> Cotraversal s t a b
cotraversal bsa bt = colens bsa bt . corepn cotraverse

-- | Obtain a 'Cotraversal' by embedding a reversed lens getter and setter into a 'Distributive' functor.
--
-- @
--  'withColens' o 'cotraversing' ≡ 'cotraversed' . o
-- @
--
cotraversing :: Distributive g => (b -> s -> a) -> (b -> t) -> Cotraversal (g s) (g t) a b
cotraversing bsa bt = corepn cotraverse . colens bsa bt 

{-
-- | Obtain a 'Cotraversal' by embedding a grate continuation into a 'Distributive' functor. 
--
-- @
--  'withGrate' o 'retraversing' ≡ 'cotraversed' . o
-- @
--
retraversing :: Distributive g => (((s -> a) -> b) -> t) -> Cotraversal (g s) (g t) a b
retraversing sabt = corepn cotraverse . grate sabt
-}

-- | Obtain a profunctor 'Cotraversal' from a Van Laarhoven 'Cotraversal'.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @abst extract ≡ extract@
--
-- * @abst f . fmap (abst g) ≡ abst (f . fmap g . getCompose) . Compose@
--
-- See 'Data.Profunctor.Optic.Property'.
--
cotraversalVl :: (forall f. Comonad f => (f a -> b) -> f s -> t) -> Cotraversal s t a b
cotraversalVl abst = cotabulate . abst . cosieve 

-- | TODO: Document
--
cotraversed :: Distributive f => Cotraversal (f a) (f b) a b 
cotraversed = cotraversalVl cotraverse
{-# INLINE cotraversed #-}

---------------------------------------------------------------------
-- Optics
---------------------------------------------------------------------

-- | TODO: Document
--
traversed :: Traversable f => Traversal (f a) (f b) a b
traversed = traversalVl traverse

-- | TODO: Document
--
itraversedRep :: F.Representable f => Traversable f => Ixtraversal (F.Rep f) (f a) (f b) a b
itraversedRep = itraversalVl F.itraverseRep

-- | TODO: Document
--
-- >>> withTraversal both (pure . length) ("hello","world")
-- (5,5)
--
both :: Traversal (a , a) (b , b) a b
both p = p **** p

-- | Duplicate the results of any 'Moore'. 
--
-- >>> lists (both . duplicated) ("hello","world")
-- ["hello","hello","world","world"]
--
duplicated :: Traversal a b a b
duplicated p = pappend p p

-- | Traverse both parts of a 'Bitraversable' container with matching types.
--
-- >>> withTraversal bitraversed (pure . length) (Right "hello")
-- Right 5
--
-- >>> withTraversal bitraversed (pure . length) ("hello","world")
-- (5,5)
--
-- >>> ("hello","world") ^. bitraversed
-- "helloworld"
--
-- @
-- 'bitraversed' :: 'Traversal' (a , a) (b , b) a b
-- 'bitraversed' :: 'Traversal' (a + a) (b + b) a b
-- @
--
bitraversed :: Bitraversable f => Traversal (f a a) (f b b) a b
bitraversed = repn $ \f -> bitraverse f f
{-# INLINE bitraversed #-}

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | 
--
-- The traversal laws can be stated in terms of 'withTraversal':
-- 
-- * @withTraversal t (Identity . f) ≡  Identity (fmap f)@
--
-- * @Compose . fmap (withTraversal t f) . withTraversal t g ≡ withTraversal t (Compose . fmap f . g)@
--
withTraversal :: Applicative f => ATraversal f s t a b -> (a -> f b) -> s -> f t
withTraversal o = runStar #. o .# Star

-- |
--
-- @
-- 'withCotraversal' $ 'Data.Profuncto.Optic.Grate.grate' (flip 'Data.Distributive.cotraverse' id) ≡ 'Data.Distributive.cotraverse'
-- @
--
-- The cotraversal laws can be restated in terms of 'withCotraversal':
--
-- * @withCotraversal o (f . extract) ≡  fmap f . extract@
--
-- * @withCotraversal o f . fmap (withCotraversal o g) == withCotraversal o (f . fmap g . getCompose) . Compose@
--
-- See also < https://www.cs.ox.ac.uk/jeremy.gibbons/publications/iterator.pdf >
--
withCotraversal :: Comonad f => ACotraversal f s t a b -> (f a -> b) -> (f s -> t)
withCotraversal o = runCostar #. o .# Costar

-- |
--
-- @
-- 'withMealy' 'cotraversed' :: 'Distributive' f => (x -> a -> (b, x)) -> x -> a -> 'NonEmpty' (f a) -> f b
-- @
--
withMealy :: Optic Mealy s t a b -> (x -> a -> (b, x)) -> x -> a -> NonEmpty s -> t
withMealy o f s a = cosieve $ o (mealy f s a)

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | TODO: Document
--
sequences :: Applicative f => ATraversal f s t (f a) a -> s -> f t
sequences o = withTraversal o id
{-# INLINE sequences #-}

-- | TODO: Document
--
distributes :: Comonad f => ACotraversal f s t a (f a) -> f s -> t
distributes o = withCotraversal o id
{-# INLINE distributes #-}

---------------------------------------------------------------------
-- Carriers
---------------------------------------------------------------------

-- | A Mealy Machine
data Mealy a b = forall s. Mealy (s -> a -> s) (a -> s) (s -> b)

mealy :: (s -> a -> (b, s)) -> s -> a -> Mealy a b
mealy f s a = Mealy (\x y -> snd $ f x y) (snd . f s) (fst . flip f a)
{-# INLINE mealy #-}

instance Semigroup b => Semigroup (Mealy a b) where
  (<>) = liftA2 (<>)
  {-# INLINE (<>) #-}

instance Monoid b => Monoid (Mealy a b) where
  mempty = pure mempty
  {-# INLINE mempty #-}

  mappend = liftA2 mappend
  {-# INLINE mappend #-}

instance (Semiring b, Monoid b) => Semiring (Mealy a b) where
  (><) = liftA2 (><)
  {-# INLINE (><) #-}

  fromBoolean = pure . fromBoolean

instance Functor (Mealy a) where
  fmap f (Mealy h z k) = Mealy h z (f . k)
  {-# INLINE fmap #-}
  b <$ _ = pure b
  {-# INLINE (<$) #-}

instance Apply (Mealy a) where
  (<.>) = (<*>)
  {-# INLINE (<.>) #-}
  (<.) m = \_ -> m
  {-# INLINE (<.) #-}
  _ .> m = m
  {-# INLINE (.>) #-}

instance Applicative (Mealy a) where
  pure x = Mealy (\() _ -> ()) (\_ -> ()) (\() -> x)
  {-# INLINE pure #-}
  Mealy hf zf kf <*> Mealy ha za ka = Mealy
    (\(Pair x y) a -> Pair (hf x a) (ha y a))
    (\a -> Pair (zf a) (za a))
    (\(Pair x y) -> kf x (ka y))
  (<*) m = \ _ -> m
  {-# INLINE (<*) #-}
  _ *> m = m
  {-# INLINE (*>) #-}

instance Monad (Mealy a) where
  return = pure
  {-# INLINE return #-}
  m >>= f = Mealy Snoc1 First (\xs a -> walk xs (f a)) <*> m
  {-# INLINE (>>=) #-}
  (>>) = (*>)
  {-# INLINE (>>) #-}

instance MonadZip (Mealy a) where
  mzipWith = liftA2
  {-# INLINE mzipWith #-}

instance MonadFix (Mealy a) where
  mfix = F.mfixRep

instance Semigroupoid Mealy where
  o = (.)
  {-# INLINE o #-}

instance Category Mealy where
  id = arr id
  {-# INLINE id #-}
  Mealy h z k . Mealy h' z' k' = Mealy h'' z'' (\(Pair b _) -> k b) where
    z'' a = Pair (z (k' b)) b where b = z' a
    h'' (Pair c d) a = Pair (h c (k' d')) d' where d' = h' d a
  {-# INLINE (.) #-}

instance Arrow Mealy where
  arr h = Mealy (\_ a -> a) id h
  {-# INLINE arr #-}
  first (Mealy h z k) = Mealy h' (first z) (first k) where
    h' (a,_) (c,b) = (h a c, b)
  {-# INLINE first #-}
  second (Mealy h z k) = Mealy h' (second z) (second k) where
    h' (_,b) (a,c) = (a, h b c)
  {-# INLINE second #-}
  Mealy h z k *** Mealy h' z' k' = Mealy h'' (z *** z') (k *** k') where
    h'' (a,b) (c,d) = (h a c, h' b d)
  {-# INLINE (***) #-}
  Mealy h z k &&& Mealy h' z' k' = Mealy h'' (z &&& z') (k *** k') where
    h'' (c,d) a = (h c a, h' d a)
  {-# INLINE (&&&) #-}

instance Profunctor Mealy where
  dimap f g (Mealy h z k) = Mealy (\a -> h a . f) (z . f) (g . k)
  {-# INLINE dimap #-}
  lmap f (Mealy h z k) = Mealy (\a -> h a . f) (z . f) k
  {-# INLINE lmap #-}
  rmap g (Mealy h z k) = Mealy h z (g . k)
  {-# INLINE rmap #-}
  ( #. ) _ = unsafeCoerce
  {-# INLINE (#.) #-}
  x .# _ = unsafeCoerce x
  {-# INLINE (.#) #-}

instance Choice Mealy where
  left' (Mealy h z k) = Mealy step (left' `id` z) (left' `id` k) where
    step (Left x) (Left y) = Left (h x y)
    step (Right c) _ = Right c
    step _ (Right c) = Right c
  {-# INLINE left' #-}

  right' (Mealy h z k) = Mealy step (right' `id` z) (right' `id` k) where
    step (Right x) (Right y) = Right (h x y)
    step (Left c) _ = Left c
    step _ (Left c) = Left c
  {-# INLINE right' #-}

instance ArrowChoice Mealy where
  left (Mealy h z k) = Mealy step (left' `id` z) (left' `id` k) where
    step (Left x) (Left y) = Left (h x y)
    step (Right c) _ = Right c
    step _ (Right c) = Right c
  {-# INLINE left #-}

  right (Mealy h z k) = Mealy step (right' `id` z) (right' `id` k) where
    step (Right x) (Right y) = Right (h x y)
    step (Left c) _ = Left c
    step _ (Left c) = Left c
  {-# INLINE right #-}

instance Strong Mealy where
  first' = first
  {-# INLINE first' #-}
  second' = second
  {-# INLINE second' #-}

instance Costrong Mealy where
  unfirst = unfirstCorep
  unsecond = unsecondCorep

instance Distributive (Mealy a) where
  distribute = F.distributeRep
  --distribute x = Mealy (\fm a -> fmap (prefix1 a) fm) x (fmap extract)

instance Closed Mealy where
  closed (Mealy h z k) = Mealy (liftA2 h) (fmap z) (\f x -> k (f x))

instance Cosieve Mealy NonEmpty where
  cosieve (Mealy h z k) (a :| as) = k (foldl h (z a) as)

instance Profunctor.Corepresentable Mealy where
  type Corep Mealy = NonEmpty
  cotabulate f = Mealy (flip (:)) pure (f . NonEmpty.fromList . Prelude.reverse)
  {-# INLINE cotabulate #-}

instance F.Representable (Mealy a) where
  type Rep (Mealy a) = NonEmpty a
  tabulate = cotabulate
  index = cosieve

instance MonadReader (NonEmpty a) (Mealy a) where
  ask = F.askRep
  local = F.localRep

walk :: SnocList1 a -> Mealy a b -> b
walk xs0 (Mealy h z k) = k (go xs0) where
  go (First a) = z a
  go (Snoc1 as a) = h (go as) a
{-# INLINE walk #-}

data SnocList1 a = Snoc1 (SnocList1 a) a | First a
  deriving (Eq,Ord,Show)

instance Functor SnocList1 where
  fmap f (Snoc1 xs x) = Snoc1 (fmap f xs) (f x)
  fmap f (First a) = First (f a)
  {-# INLINABLE fmap #-}

instance Foldable SnocList1 where
  foldl f z m0 = go m0 where
    go (Snoc1 xs x) = f (go xs) x
    go (First a) = f z a
  {-# INLINE foldl #-}
  foldl1 f m0 = go m0 where
    go (Snoc1 xs x) = f (go xs) x
    go (First a) = a
  {-# INLINE foldl1 #-}
  foldMap f (Snoc1 xs x) = foldMap f xs `mappend` f x
  foldMap f (First a) = f a
  {-# INLINABLE foldMap #-}

instance Traversable SnocList1 where
  traverse f (Snoc1 xs x) = Snoc1 <$> traverse f xs <*> f x
  traverse f (First a) = First <$> f a
  {-# INLINABLE traverse #-}

-- | Strict Pair
data Pair a b = Pair !a !b deriving (Eq,Ord,Show)

instance (Semigroup a, Semigroup b) => Semigroup (Pair a b) where
  Pair a b <> Pair c d = Pair (a <> c) (b <> d)
  {-# INLINE (<>) #-}

instance (Monoid a, Monoid b) => Monoid (Pair a b) where
  mempty = Pair mempty mempty
  {-# INLINE mempty #-}

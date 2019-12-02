{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Lens (
    -- * Lens & Ixlens
    Lens
  , Ixlens
  , Lens'
  , Ixlens'
  , lens
  , ixlens
  , lensVl
  , ixlensVl
  , matching
  , cloneLens
    -- * Colens & Cxlens
  , Colens
  , Cxlens
  , Colens'
  , Cxlens'
  , colens
  --, cxlens
  , colensVl
  , comatching
  --, cloneColens
    -- * Optics
  , ixfirst
  , cofirst
  , ixsecond
  , cosecond
  , united
  , voided
  , valued
  , root
  , branches
    -- * Primitive operators
  , withLens
  , withIxlens
  --, withColens
    -- * Operators
  , toPastro
  , toTambara
    -- * Carriers
  , ALens
  , ALens'
  , AIxlens
  , AIxlens'
  , LensRep(..)
  , IxlensRep(..)
 -- , AColens
 -- , AColens'
  --, ColensRep(..)
    -- * Classes
  , Strong(..)
  , Costrong(..)
) where

import Data.Profunctor.Strong
import Data.Profunctor.Optic.Iso
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Index
import Data.Profunctor.Optic.Type
import Data.Tree
import Data.Void (Void, absurd)
import GHC.Generics hiding (from, to)
import qualified Data.Bifunctor as B

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> import Data.Tree
-- >>> import Data.Int.Instance
-- >>> :load Data.Profunctor.Optic

---------------------------------------------------------------------
-- 'Lens' & 'Ixlens'
---------------------------------------------------------------------

-- | Obtain a 'Lens' from a getter and setter.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input functions satisfy the following
-- properties:
--
-- * @sa (sbt s a) ≡ a@
--
-- * @sbt s (sa s) ≡ s@
--
-- * @sbt (sbt s a1) a2 ≡ sbt s a2@
--
-- See 'Data.Profunctor.Optic.Property'.
--
lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens sa sbt = dimap (id &&& sa) (uncurry sbt) . second'
{-# INLINE lens #-}

-- | Obtain an indexed 'Lens' from an indexed getter and a setter.
--
-- Compare 'lens' and 'Data.Profunctor.Optic.Traversal.ixtraversal'.
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
ixlens :: (s -> (i , a)) -> (s -> b -> t) -> Ixlens i s t a b
ixlens sia sbt = ixlensVl $ \iab s -> sbt s <$> uncurry iab (sia s)
{-# INLINE ixlens #-}

-- | Transform a Van Laarhoven lens into a profunctor lens.
--
-- Compare 'Data.Profunctor.Optic.Grate.grateVl' and 'Data.Profunctor.Optic.Traversal.traversalVl'.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @abst Identity ≡ Identity@
--
-- * @fmap (abst f) . (abst g) ≡ getCompose . abst (Compose . fmap f . g)@
--
-- More generally, a profunctor optic must be monoidal as a natural 
-- transformation:
-- 
-- * @o id ≡ id@
--
-- * @o ('Data.Profunctor.Composition.Procompose' p q) ≡ 'Data.Profunctor.Composition.Procompose' (o p) (o q)@
--
lensVl :: (forall f. Functor f => (a -> f b) -> s -> f t) -> Lens s t a b
lensVl o = dimap ((info &&& values) . o (flip Index id)) (uncurry id . swap) . first'
{-# INLINE lensVl #-}

-- | Transform an indexed Van Laarhoven lens into an indexed profunctor 'Lens'.
--
-- An 'Ixlens' is a valid 'Lens' and a valid 'IxTraversal'. 
--
-- Compare 'lensVl' & 'Data.Profunctor.Optic.Traversal.ixtraversalVl'.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @iabst (const Identity) ≡ Identity@
--
-- * @fmap (iabst $ const f) . (iabst $ const g) ≡ getCompose . iabst (const $ Compose . fmap f . g)@
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
ixlensVl :: (forall f. Functor f => (i -> a -> f b) -> s -> f t) -> Ixlens i s t a b
ixlensVl f = lensVl $ \iab -> f (curry iab) . snd
{-# INLINE ixlensVl #-}

-- | Obtain a 'Lens' from its free tensor representation.
--
matching :: (s -> (c , a)) -> ((c , b) -> t) -> Lens s t a b
matching sca cbt = dimap sca cbt . second'

-- | TODO: Document
--
cloneLens :: ALens s t a b -> Lens s t a b
cloneLens o = withLens o lens 

---------------------------------------------------------------------
-- 'Colens' & 'Cxlens'
---------------------------------------------------------------------

-- | Obtain a 'Colens' from a getter and setter. 
--
-- @
-- 'colens' f g ≡ \\f g -> 're' ('lens' f g)
-- 'colens' bsia bt ≡ 'colensVl' '$' \\ts b -> bsia b '<$>' (ts . bt '$' b)
-- 'review' $ 'colens' f g ≡ f
-- 'set' . 're' $ 're' ('lens' f g) ≡ g
-- @
--
-- A 'Colens' is a 'Review', so you can specialise types to obtain:
--
-- @ 'review' :: 'Colens'' s a -> a -> s @
--
-- /Caution/: In addition to the normal optic laws, the input functions
-- must have the correct < https://wiki.haskell.org/Lazy_pattern_match laziness > annotations.
--
-- For example, this is a perfectly valid 'Colens':
--
-- @
-- co1 :: Colens a b (a, c) (b, c)
-- co1 = flip colens fst $ \ ~(_,y) b -> (b,y)
-- @
--
-- However removing the annotation will result in a faulty optic.
-- 
-- See 'Data.Profunctor.Optic.Property'.
--
colens :: (b -> s -> a) -> (b -> t) -> Colens s t a b
colens bsa bt = unsecond . dimap (uncurry bsa) (id &&& bt)

-- | Transform a Van Laarhoven colens into a profunctor colens.
--
-- Compare 'Data.Profunctor.Optic.Grate.grateVl'.
--
-- /Caution/: In addition to the normal optic laws, the input functions
-- must have the correct laziness annotations.
--
-- For example, this is a perfectly valid 'Colens':
--
-- @ 
-- co1 = colensVl $ \f ~(a,b) -> (,b) <$> f a
-- @
--
-- However removing the annotation will result in a faulty optic.
-- 
colensVl :: (forall f. Functor f => (t -> f s) -> b -> f a) -> Colens s t a b
colensVl o = unfirst . dimap (uncurry id . swap) ((info &&& values) . o (flip Index id))

-- | Obtain a 'Colens' from its free tensor representation.
--
comatching :: ((c , s) -> a) -> (b -> (c , t)) -> Colens s t a b
comatching csa bct = unsecond . dimap csa bct

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | Extract the two functions that characterize a 'Lens'.
--
withLens :: ALens s t a b -> ((s -> a) -> (s -> b -> t) -> r) -> r
withLens o f = case o (LensRep id (flip const)) of LensRep x y -> f x y

---------------------------------------------------------------------
-- Optics 
---------------------------------------------------------------------

-- | TODO: Document
--
cofirst :: Colens a b (a , c) (b , c)
cofirst = unfirst

-- | TODO: Document
--
cosecond :: Colens a b (c , a) (c , b)
cosecond = unsecond

-- | TODO: Document
--
-- >>> ixlists (ix @Int traversed . ix first' . ix traversed) [("foo",1), ("bar",2)]
-- [(0,'f'),(1,'o'),(2,'o'),(0,'b'),(1,'a'),(2,'r')]
--
-- >>> ixlists (ix @Int traversed . ixfirst . ix traversed) [("foo",1), ("bar",2)]
-- [(0,'f'),(1,'o'),(2,'o'),(0,'b'),(1,'a'),(2,'r')]
--
-- >>> ixlists (ix @Int traversed % ix first' % ix traversed) [("foo",1), ("bar",2)]
-- [(0,'f'),(1,'o'),(2,'o'),(1,'b'),(2,'a'),(3,'r')]
--
-- >>> ixlists (ix @Int traversed % ixfirst % ix traversed) [("foo",1), ("bar",2)]
-- [(0,'f'),(1,'o'),(2,'o'),(2,'b'),(3,'a'),(4,'r')]
--
ixfirst :: Ixlens i (a , c) (b , c) a b
ixfirst = lmap assocl . first'

-- | TODO: Document
--
ixsecond :: Ixlens i (c , a) (c , b) a b
ixsecond = lmap (\(i, (c, a)) -> (c, (i, a))) . second'

-- | There is a `Unit` in everything.
--
-- >>> "hello" ^. united
-- ()
-- >>> "hello" & united .~ ()
-- "hello"
--
united :: Lens' a ()
united = lens (const ()) const

-- | There is everything in a `Void`.
--
-- >>> [] & fmapped . voided <>~ "Void" 
-- []
-- >>> Nothing & fmapped . voided ..~ abs
-- Nothing
--
voided :: Lens' Void a
voided = lens absurd const

-- | TODO: Document
--
-- Compare 'Data.Profunctor.Optic.Prism.keyed'.
--
valued :: Eq k => k -> Lens' (k -> v) v
valued k = lens ($ k) (\g v' x -> if (k == x) then v' else g x)

-- | A 'Lens' that focuses on the root of a 'Tree'.
--
-- >>> view root $ Node 42 []
-- 42
--
root :: Lens' (Tree a) a
root = lensVl $ \f (Node a as) -> (`Node` as) <$> f a
{-# INLINE root #-}

-- | A 'Lens' returning the direct descendants of the root of a 'Tree'
--
-- @'Data.Profunctor.Optic.View.view' 'branches' ≡ 'subForest'@
--
branches :: Lens' (Tree a) [Tree a]
branches = lensVl $ \f (Node a as) -> Node a <$> f as
{-# INLINE branches #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Use a 'Lens' to construct a 'Pastro'.
--
toPastro :: ALens s t a b -> p a b -> Pastro p s t
toPastro o p = withLens o $ \sa sbt -> Pastro (uncurry sbt . swap) p (\s -> (sa s, s))

-- | Use a 'Lens' to construct a 'Tambara'.
--
toTambara :: Strong p => ALens s t a b -> p a b -> Tambara p s t
toTambara o p = withLens o $ \sa sbt -> Tambara (first' . lens sa sbt $ p)

---------------------------------------------------------------------
-- LensRep
---------------------------------------------------------------------

-- | The `LensRep` profunctor precisely characterizes a 'Lens'.
--
data LensRep a b s t = LensRep (s -> a) (s -> b -> t)

type ALens s t a b = Optic (LensRep a b) s t a b

type ALens' s a = ALens s s a a

instance Profunctor (LensRep a b) where
  dimap f g (LensRep sa sbt) = LensRep (sa . f) (\s -> g . sbt (f s))

instance Strong (LensRep a b) where
  first' (LensRep sa sbt) =
    LensRep (\(a, _) -> sa a) (\(s, c) b -> (sbt s b, c))

  second' (LensRep sa sbt) =
    LensRep (\(_, a) -> sa a) (\(c, s) b -> (c, sbt s b))

instance Sieve (LensRep a b) (Index a b) where
  sieve (LensRep sa sbt) s = Index (sa s) (sbt s)

instance Representable (LensRep a b) where
  type Rep (LensRep a b) = Index a b

  tabulate f = LensRep (\s -> info (f s)) (\s -> values (f s))

---------------------------------------------------------------------
-- IxlensRep
---------------------------------------------------------------------

data IxlensRep i a b s t = IxlensRep (s -> (i , a)) (s -> b -> t)

type AIxlens i s t a b = IndexedOptic (IxlensRep i a b) i s t a b

type AIxlens' i s a = AIxlens i s s a a

instance Profunctor (IxlensRep i a b) where
  dimap f g (IxlensRep sia sbt) = IxlensRep (sia . f) (\s -> g . sbt (f s))

instance Strong (IxlensRep i a b) where
  first' (IxlensRep sia sbt) =
    IxlensRep (\(a, _) -> sia a) (\(s, c) b -> (sbt s b, c))

  second' (IxlensRep sia sbt) =
    IxlensRep (\(_, a) -> sia a) (\(c, s) b -> (c, sbt s b))

-- | Extract the two functions that characterize a 'Lens'.
--
withIxlens :: Monoid i => AIxlens i s t a b -> ((s -> (i , a)) -> (s -> b -> t) -> r) -> r
withIxlens o f = case o (IxlensRep id $ flip const) of IxlensRep x y -> f (x . (mempty,)) (\s b -> y (mempty, s) b)

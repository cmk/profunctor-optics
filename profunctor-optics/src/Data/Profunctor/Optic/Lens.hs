{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# OPTIONS_GHC -fno-warn-duplicate-exports #-}

-- | Left and right carriers are characterized by their representation
-- functors ('Rep' and 'Corep'). 'Iso' sits at the top where both
-- are trivial ('Identity'). 'Adjoint' sits at the bottom where they
-- form a full adjunction (@'Corep' p ⊣ 'Rep' p@). A left-indexed
-- ('Ix') optic threads an index through the left adjoint functor
-- @(,) k@, while a right-indexed ('Cx') optic threads a coindex
-- through the right adjoint functor @(->) k@.
module Data.Profunctor.Optic.Lens (
    -- * Constructors
    -- ** Lens, Ixlens
    Lens, Lens'
  , Ixlens, Ixlens'
  , lens
  , ixlens
  , lensVl
  , ixlensVl
  , matching
  , cloneLens
  , cloneLensVl
  , cloneIxlens
  , cloneIxlensVl
    -- * Dual Constructors
    -- ** Colens, Cxlens
  , Colens, Colens'
  , Cxlens, Cxlens'
  , colens
  , cxlens
  , colensVl
  , cxlensVl
  , grate
  , grate'
  , grateVl
  , comatching
  , inside
  , cloneColens
  , cloneColensVl
  , cloneCxlens
  , cloneCxlensVl
    -- ** Relens, Rxlens
  , Relens, Relens'
  , Rxlens, Rxlens'
  , relens
  , relensVl
  , rematching
  , rematching'
  , cloneRelens
  , cloneRelensVl
  , rxlens
  , rxlensVl
    -- * Optics
    -- ** Lens, Ixlens
  , first, second
  , ixfirst, ixsecond
  , united
  , voided
    -- ** Colens, Cxlens
  , cofirst, cosecond
  , cxfirst, cxsecond
  , grated
  , cxgrated
  , represented
  , distributed
  , endomorphed
  , continued
  , continuedT
    -- ** Relens, Rxlens
  , refirst, resecond
    -- * Operators
    -- ** Lens, Ixlens
  , pastro
  , tambara
  , withLens
  , withIxlens
    -- * Dual Operators
    -- ** Colens, Cxlens
  , coview
  , cxzips
  , zipsWith
  , zipsWith3
  , zipsWith4
  , zipsWithF
  , closure
  , environment
  , withColens
  , withCxlens
    -- ** Relens, Rxlens
  , reover
  , withRelens
    -- * MTL
  , calledCC
    -- * Reexports
  , Strong(..)
  , Closed(..)
  , Costrong(..)
) where

import Control.Monad.Cont
import Data.Profunctor.Closed (Closure(..), Environment(..), curry')
import Data.Profunctor.Rep (unfirstCorep, unsecondCorep)
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Arrow
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Iso
import Data.Profunctor.Optic.Types
import Data.Profunctor.Strong hiding (pastro, tambara)
import qualified Data.Functor.Rep as F

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XTypeFamilies
-- >>> :set -XFlexibleContexts
-- >>> :set -XTupleSections
-- >>> import Control.Arrow ((&&&))
-- >>> import Control.Monad.Reader
-- >>> import Data.Int
-- >>> import Data.Complex
-- >>> import Data.Tuple (swap)
-- >>> import Data.Function ((&))
-- >>> import Data.List as L
-- >>> import Data.Monoid (Endo(..))
-- >>> import Data.Semigroup
-- >>> import qualified Data.Bifunctor as B
-- >>> import qualified Data.ByteString as B
-- >>> import qualified Data.ByteString.Char8 as C
-- >>> :load Data.Profunctor.Optic
-- >>> import Prelude

---------------------------------------------------------------------
-- Constructors
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
lens sa sbt = dimap (fanout id sa) (uncurry sbt) . second'
{-# INLINE lens #-}

-- | Obtain an indexed 'Lens' from an indexed getter and a setter.
--
-- Compare 'lens' and 'Data.Profunctor.Optic.Traversal.itraversal'.
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
-- @since 0.0.3
ixlens :: (s -> (k , a)) -> (s -> b -> t) -> Ixlens k s t a b
ixlens ska sbt = ixlensVl $ \kab _k s -> sbt s <$> uncurry kab (ska s)
{-# INLINE ixlens #-}

-- | Transform a Van Laarhoven lens into a profunctor lens.
--
-- Compare 'Data.Profunctor.Optic.Lens.grateVl' and 'Data.Profunctor.Optic.Traversal.traversalVl'.
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
lensVl abst = dimap ((fanout info vals) . abst (flip Index id)) (uncurry id . swap) . first'
{-# INLINE lensVl #-}

-- | Transform an indexed Van Laarhoven lens into an indexed profunctor 'Lens'.
--
-- An 'Ixlens' is a valid 'Ixtraversal'. Compare 'Data.Profunctor.Optic.Traversal.itraversalVl'.
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
-- @since 0.0.3
ixlensVl :: (forall f. Functor f => (k -> a -> f b) -> k -> s -> f t) -> Ixlens k s t a b
ixlensVl f = lensVl $ \iab -> uncurry (f (curry iab))
{-# INLINE ixlensVl #-}

-- | Obtain a 'Lens' from its free tensor representation.
--
matching :: (s -> (c , a)) -> ((c , b) -> t) -> Lens s t a b
matching sca cbt = dimap sca cbt . second'

-- | TODO: Document
--
cloneLens :: ALens s t a b -> Lens s t a b
cloneLens o = withLens o $ \sa sbt -> lens sa sbt

-- | Extract the higher order function that characterizes a 'Lens'.
--
-- The lens laws can be stated in terms of 'withLens':
--
-- Identity:
--
-- @
-- cloneLensVl o Identity ≡ Identity
-- @
--
-- Composition:
--
-- @
-- Compose . fmap (cloneLensVl o f) . cloneLensVl o g ≡ cloneLensVl o (Compose . fmap f . g)
-- @
--
-- See 'Data.Profunctor.Optic.Property'.
--
cloneLensVl :: ALens s t a b -> (forall f . Functor f => (a -> f b) -> s -> f t)
cloneLensVl o ab s = withLens o $ \sa sbt -> sbt s <$> ab (sa s)
{-# INLINE cloneLensVl #-}

-- | Clone an 'Ixlens'.
--
-- @since 0.0.3
cloneIxlens :: AIxlens k s t a b -> Ixlens k s t a b
cloneIxlens o = withIxlens o $ \ska sbt -> ixlens ska sbt
{-# INLINE cloneIxlens #-}

-- | Extract the indexed Van Laarhoven form of an 'Ixlens'.
--
-- @since 0.0.3
cloneIxlensVl :: AIxlens k s t a b -> (forall f. Functor f => (k -> a -> f b) -> k -> s -> f t)
cloneIxlensVl o kab _k s = withIxlens o $ \ska sbt -> sbt s <$> uncurry kab (ska s)
{-# INLINE cloneIxlensVl #-}

---------------------------------------------------------------------
-- Dual Constructors
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
-- /Caution/: Colenses are recursive, similar to < http://hackage.haskell.org/package/base-4.12.0.0/docs/Control-Arrow.html#t:ArrowLoop ArrowLoop >.
-- In addition to the normal optic laws, the input functions must have
-- the correct < https://wiki.haskell.org/Lazy_pattern_match laziness > annotations.
--
-- For example, this is a perfectly valid 'Colens':
--
-- @
-- ct21 :: Colens a b (a, c) (b, c)
-- ct21 = flip colens fst $ \ ~(_,c) b -> (b,c)
-- @
--
-- However removing the annotation will result in a faulty optic.
--
-- See 'Data.Profunctor.Optic.Property'.
--
colens :: (b -> s -> a) -> (b -> t) -> Colens s t a b
colens bsa bt = cosecond . dimap (uncurry bsa) (fanout id bt)

-- | TODO: Document
--
-- @since 0.0.3
cxlens :: (((s -> a) -> k -> b) -> t) -> Cxlens k s t a b
cxlens f = cxlensVl $ \aib s _k -> f $ \sa -> aib (fmap sa s)
{-# INLINE cxlens #-}

-- | Transform a Van Laarhoven colens into a profunctor colens.
--
-- Compare 'grateVl'.
--
-- /Caution/: In addition to the normal optic laws, the input functions
-- must have the correct laziness annotations.
--
-- For example, this is a perfectly valid 'Colens':
--
-- @
-- ct21 :: Colens a b (a, c) (b, c)
-- ct21 = colensVl $ \f ~(a,b) -> (,b) <$> f a
-- @
--
-- However removing the annotation will result in a faulty optic.
--
colensVl :: (forall f. Functor f => (t -> f s) -> b -> f a) -> Colens s t a b
colensVl o = cofirst . dimap (uncurry id . swap) ((fanout info vals) . o (flip Index id))

-- | Transform a coindexed Van Laarhoven grate into a coindexed profunctor grate.
--
-- @since 0.0.3
cxlensVl :: (forall f. Functor f => (f a -> k -> b) -> f s -> k -> t) -> Cxlens k s t a b
cxlensVl = grateVl
{-# INLINE cxlensVl #-}

-- | Obtain a 'Colens' from a nested continuation.
--
-- The resulting optic is the corepresentable counterpart to 'Lens',
-- and sits between 'Iso' and 'Setter'.
--
-- A 'Colens' lets you lift a profunctor through any representable
-- functor (aka Naperian container). In the special case where the
-- indexing type is finitary (e.g. 'Bool') then the tabulated type is
-- isomorphic to a fixed length vector (e.g. 'V2 a').
--
-- The identity container is representable, and representable functors
-- are closed under composition.
--
-- See <https://www.cs.ox.ac.uk/jeremy.gibbons/publications/proyo.pdf>
-- section 4.6 for more background on 'Colens's, and compare to the
-- /lens-family/ <http://hackage.haskell.org/package/lens-family-2.0.0/docs/Lens-Family2.html#t:Colens version>.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input function satisfies the following
-- properties:
--
-- * @sabt ($ s) ≡ s@
--
-- * @sabt (\k -> f (k . sabt)) ≡ sabt (\k -> f ($ k))@
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
grate :: (((s -> a) -> b) -> t) -> Colens s t a b
grate f = dimap (flip ($)) f . closed
{-# INLINE grate #-}

-- | Construct a 'Colens' from a pair of inverses.
--
grate' :: (s -> a) -> (b -> t) -> Colens s t a b
grate' sa bt = grate $ \sab -> bt (sab sa)
{-# INLINE grate' #-}

-- | Transform a Van Laarhoven grate into a profunctor grate.
--
-- Compare 'Data.Profunctor.Optic.Lens.lensVl' & 'Data.Profunctor.Optic.Traversal.cotraversalVl'.
--
-- /Caution/: In order for the generated family to be well-defined,
-- you must ensure that the traversal1 law holds for the input function:
--
-- * @abst runIdentity ≡ runIdentity@
--
-- * @abst f . fmap (abst g) ≡ abst (f . fmap g . getCompose) . Compose@
--
-- See 'Data.Profunctor.Optic.Property'.
--
grateVl :: (forall f. Functor f => (f a -> b) -> f s -> t) -> Colens s t a b
grateVl o = dimap (curry eval) ((o trivial) . Coindex) . closed
{-# INLINE grateVl #-}

-- | Obtain a 'Colens' from its free tensor representation.
--
-- >>> fib = comatching (uncurry L.take . swap) (fanout id L.reverse) --fib :: Colens Int [Int] [Int] [Int]
-- >>> 10 & fib ..~ \xs -> 1 : 1 : Prelude.zipWith (+) xs (drop 1 xs)
-- [89,55,34,21,13,8,5,3,2,1,1]
--
comatching :: ((c , s) -> a) -> (b -> (c , t)) -> Colens s t a b
comatching csa bct = cosecond . dimap csa bct

-- | Lift a 'Lens' so it can run under a function (or other corepresentable profunctor).
--
-- @
-- 'inside' :: 'Lens' s t a b -> 'Lens' (e -> s) (e -> t) (e -> a) (e -> b)
-- @
--
-- >>> (\x -> (x-1,x+1)) ^. inside first $ 5
-- 4
--
inside :: Corepresentable p => ALens s t a b -> Lens (p e s) (p e t) (p e a) (p e b)
inside l = lensVl $ \f es -> o es <$> f (k es) where
  k es = cotabulate $ \ e -> info $ cloneLensVl l sell (cosieve es e)
  o es ea = cotabulate $ \ e -> flip vals (cosieve ea e) $ cloneLensVl l sell (cosieve es e)
  sell x = Index x id
{-# INLINE inside #-}

-- | TODO: Document
--
cloneColens :: AColens s t a b -> Colens s t a b
cloneColens k = withColens k $ \sabt -> grate sabt
{-# INLINE cloneColens #-}

-- | Extract the higher order function that characterizes a 'Colens'.
--
-- The grate laws can be stated in terms or 'withColens':
--
-- Identity:
--
-- @
-- cloneColensVl o runIdentity ≡ runIdentity
-- @
--
-- Composition:
--
-- @
-- cloneColensVl o f . fmap (cloneColensVl o g) ≡ cloneColensVl o (f . fmap g . getCompose) . Compose
-- @
--
cloneColensVl :: AColens s t a b -> (forall f . Functor f => (f a -> b) -> f s -> t)
cloneColensVl o ab s = withColens o $ \sabt -> sabt $ \sa -> ab (fmap sa s)
{-# INLINE cloneColensVl #-}

-- | Clone a 'Cxlens'.
--
-- @since 0.0.3
cloneCxlens :: Monoid k => ACxlens k s t a b -> Cxlens k s t a b
cloneCxlens o = withCxlens o cxlens
{-# INLINE cloneCxlens #-}

-- | Extract the coindexed Van Laarhoven form of a 'Cxlens'.
--
-- @since 0.0.3
cloneCxlensVl :: Monoid k => ACxlens k s t a b -> (forall f. Functor f => (f a -> k -> b) -> f s -> k -> t)
cloneCxlensVl o fab fs _k = withCxlens o $ \sabt -> sabt $ \sa k -> fab (fmap sa fs) k
{-# INLINE cloneCxlensVl #-}

---------------------------------------------------------------------
-- Reversed Constructors
---------------------------------------------------------------------

-- | Obtain a 'Relens' from a co-getter and co-setter.
--
-- @'relens' bsa bt ≡ 're' ('lens' sa sbt)@ (with roles swapped)
--
-- A 'Relens' is simultaneously a 'View' and a 'Review':
--
-- @
-- 'Data.Profunctor.Optic.View.review' ('relens' bsa bt) ≡ bt
-- @
--
relens :: (b -> s -> a) -> (b -> t) -> Relens s t a b
relens bsa bt = unsecond . dimap (uncurry bsa) (fanout id bt)
{-# INLINE relens #-}

-- | Obtain a 'Relens' from its van Laarhoven representation.
--
relensVl :: (forall f. Functor f => (t -> f s) -> b -> f a) -> Relens s t a b
relensVl o = unfirst . dimap (uncurry id . swap) ((fanout info vals) . o (flip Index id))
{-# INLINE relensVl #-}

-- | Obtain a 'Relens' from its free tensor representation.
--
rematching :: (c -> s -> a) -> (b -> (c, t)) -> Relens s t a b
rematching csa bct = unsecond . dimap (uncurry csa) bct
{-# INLINE rematching #-}

-- | Obtain a 'Relens' from a single combining function.
--
-- @
-- 'rematching'' f ≡ 'rematching' f (\\a -> (a, a))
-- @
--
rematching' :: (t -> s -> a) -> Relens s t a t
rematching' f = unsecond . dimap (uncurry f) (\a -> (a, a))
{-# INLINE rematching' #-}

-- | Clone a 'Relens'.
--
cloneRelens :: ARelens s t a b -> Relens s t a b
cloneRelens o = withRelens o relens
{-# INLINE cloneRelens #-}

-- | Extract the Van Laarhoven form of a 'Relens'.
--
-- @since 0.0.3
cloneRelensVl :: ARelens s t a b -> (forall f. Functor f => (t -> f s) -> b -> f a)
cloneRelensVl o tf b = withRelens o $ \bsa bt -> bsa b <$> tf (bt b)
{-# INLINE cloneRelensVl #-}

-- | Obtain an indexed 'Relens' from an indexed getter and a setter.
--
-- @since 0.0.3
rxlens :: (b -> s -> (r , a)) -> (b -> t) -> Rxlens r s t a b
rxlens bsia bt = rxlensVl $ \ts b -> bsia b <$> (ts . bt $ b)
{-# INLINE rxlens #-}

-- | Transform an indexed Van Laarhoven relens into an indexed profunctor 'Relens'.
--
-- Compare 'ixlensVl' and 'relensVl'.
--
-- @since 0.0.3
rxlensVl :: (forall f. Functor f => (t -> f s) -> b -> f (r, a)) -> Rxlens r s t a b
rxlensVl f = relensVl $ \ts -> f (fmap snd . ts)
{-# INLINE rxlensVl #-}

---------------------------------------------------------------------
-- Optics
---------------------------------------------------------------------

-- | TODO: Document
--
first :: Lens (a, c) (b, c) a b
first = first'
{-# INLINE first #-}

-- | TODO: Document
--
second :: Lens (c, a) (c, b) a b
second = second'
{-# INLINE second #-}

-- | TODO: Document
--
-- >>> B.first getSum <$> ixtoListOf (noix traversed . ixfirst . ix (Sum 1) traversed) [("foo",1), ("bar",2)]
-- [(0,'f'),(1,'o'),(2,'o'),(0,'b'),(1,'a'),(2,'r')]
-- >>> B.first getSum <$> ixtoListOf (ix (Sum 3) traversed . ixfirst . ix (Sum 1) traversed) [("foo",1), ("bar",2)]
-- [(0,'f'),(1,'o'),(2,'o'),(3,'b'),(4,'a'),(5,'r')]
--
-- @since 0.0.3
ixfirst :: Ixlens k (a , c) (b , c) a b
ixfirst = lmap assocl . first
{-# INLINE ixfirst #-}

-- | TODO: Document
--
-- @since 0.0.3
ixsecond :: Ixlens k (c , a) (c , b) a b
ixsecond = lmap (\(i, (c, a)) -> (c, (i, a))) . second
{-# INLINE ixsecond #-}

-- | There is a '()' in everything.
--
-- >>> "hello" ^. united
-- ()
-- >>> "hello" & united .~ ()
-- "hello"
--
united :: Lens' a ()
united = lens (const ()) const
{-# INLINE united #-}

-- | There is everything in a 'Void'.
--
-- >>> Nothing & fmapped . voided ..~ abs
-- Nothing
--
voided :: Lens' Void a
voided = lens absurd const
{-# INLINE voided #-}

---------------------------------------------------------------------
-- Dual Optics
---------------------------------------------------------------------

-- | TODO: Document
--
cofirst :: Colens a b (a, c) (b, c)
cofirst = cloneColens unfirstCorep
{-# INLINE cofirst #-}

-- | TODO: Document
--
cosecond :: Colens a b (c, a) (c, b)
cosecond = cloneColens unsecondCorep
{-# INLINE cosecond #-}

-- | TODO: Document
--
-- @since 0.0.3
cxfirst :: Cxlens k a b (a , c) (b , c)
cxfirst = rmap (unfirst . uncurry . flip) . curry'
{-# INLINE cxfirst #-}

-- | TODO: Document
--
-- @since 0.0.3
cxsecond :: Cxlens k a b (c , a) (c , b)
cxsecond = rmap (unsecond . uncurry) . curry' . lmap swap
{-# INLINE cxsecond #-}

-- | TODO: Document
--
grated :: Colens (c -> a) (c -> b) a b
grated = closed
{-# INLINE grated #-}

-- | TODO: Document
--
-- >>> cxover cxgrated (,) (*2) 5
-- ((),10)
--
-- @since 0.0.3
cxgrated :: Cxlens k (c -> a) (c -> b) a b
cxgrated = rmap flip . closed
{-# INLINE cxgrated #-}

-- | Obtain a 'Colens' from a 'F.Representable' functor.
--
represented :: F.Representable f => Colens (f a) (f b) a b
represented = tabulated . closed
{-# INLINE represented #-}

-- | Obtain a 'Colens' from a distributive functor.
--
distributed :: Distributive f => Colens (f a) (f b) a b
distributed = grate (`cotraverse` id)
{-# INLINE distributed #-}

-- | Obtain a 'Colens' from an endomorphism.
--
-- >>> flip appEndo 2 $ zipsWith endomorphed (+) (Endo (*3)) (Endo (*4))
-- 14
--
endomorphed :: Colens' (Endo a) a
endomorphed = dimap appEndo Endo . closed
{-# INLINE endomorphed #-}

-- | Obtain a 'Colens' from a continuation.
--
-- @
-- 'zipsWith' 'continued' :: (a -> a -> a) -> c -> c -> 'Cont' a c
-- @
--
continued :: Colens c (Cont a c) a a
continued = grate cont
{-# INLINE continued #-}

-- | Obtain a 'Colens' from a continuation.
--
-- @
-- 'zipsWith' 'continued' :: (m a -> m a -> m a) -> c -> c -> 'ContT' a m c
-- @
--
continuedT :: Colens c (ContT a m c) (m a) (m a)
continuedT = grate ContT
{-# INLINE continuedT #-}

---------------------------------------------------------------------
-- Reversed Optics
---------------------------------------------------------------------

-- | 'Relens' into the first component of a pair.
--
-- @'refirst' ≡ 're' 'first'@
--
refirst :: Relens a b (a, c) (b, c)
refirst = unfirst
{-# INLINE refirst #-}

-- | 'Relens' into the second component of a pair.
--
-- @'resecond' ≡ 're' 'second'@
--
resecond :: Relens a b (c, a) (c, b)
resecond = unsecond
{-# INLINE resecond #-}

-- | The Re-dual of 'Data.Profunctor.Optic.Setter.over': apply a
-- function through a 'Relens', going in the reverse direction.
--
-- @
-- 'over'   :: 'ALens'   s t a b -> (a -> b) -> s -> t
-- 'reover' :: 'ARelens' s t a b -> (t -> s) -> b -> a
-- @
--
-- 'reover' accepts any optic with a 'RelensRep' carrier ('ARelens'),
-- including 'Relens', 'Iso', and any optic that is both 'Strong'
-- and 'Costrong'.
--
-- /Example/: collapse a pair-producing 'Sort' to its first component:
--
-- @
-- 'reover' 'refirst' :: (t -> s) -> (a, c) -> a
-- @
--
reover :: ARelens s t a b -> (t -> s) -> b -> a
reover o ts b = withRelens o $ \bsa bt -> bsa b (ts (bt b))
{-# INLINE reover #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Use a 'Lens' to construct a 'Pastro'.
--
pastro :: ALens s t a b -> p a b -> Pastro p s t
pastro o p = withLens o $ \sa sbt -> Pastro (uncurry sbt . swap) p (\s -> (sa s, s))
{-# INLINE pastro #-}

-- | Use a 'Lens' to construct a 'Tambara'.
--
tambara :: Strong p => ALens s t a b -> p a b -> Tambara p s t
tambara o p = withLens o $ \sa sbt -> Tambara (first' . lens sa sbt $ p)
{-# INLINE tambara #-}

---------------------------------------------------------------------
-- Dual Operators
---------------------------------------------------------------------

-- | Set all fields to the given value.
--
-- Compare 'Data.Profunctor.Optic.View.review'.
--
coview :: AColens s t a b -> b -> t
coview o b = withColens o $ \sabt -> sabt (const b)
{-# INLINE coview #-}

-- | TODO: Document
--
-- @since 0.0.3
cxzips :: Monoid k => ACxlens k s t a b -> (k -> a -> a -> b) -> s -> s -> t
cxzips o f s1 s2 = withCxlens o $ \sabt -> sabt $ \sa k -> f k (sa s1) (sa s2)
{-# INLINE cxzips #-}

-- | Zip over a 'Colens'.
--
-- @\\f -> 'zipsWith' 'closed' ('zipsWith' 'closed' f) ≡ 'zipsWith' ('closed' . 'closed')@
--
zipsWith :: AColens s t a b -> (a -> a -> b) -> s -> s -> t
zipsWith o f s1 s2 = withColens o $ \sabt -> sabt $ \sa -> f (sa s1) (sa s2)
{-# INLINE zipsWith #-}

-- | Zip over a 'Colens' with 3 arguments.
--
zipsWith3 :: AColens s t a b -> (a -> a -> a -> b) -> (s -> s -> s -> t)
zipsWith3 o f s1 s2 s3 = withColens o $ \sabt -> sabt $ \sa -> f (sa s1) (sa s2) (sa s3)
{-# INLINE zipsWith3 #-}

-- | Zip over a 'Colens' with 4 arguments.
--
zipsWith4 :: AColens s t a b -> (a -> a -> a -> a -> b) -> (s -> s -> s -> s -> t)
zipsWith4 o f s1 s2 s3 s4 = withColens o $ \sabt -> sabt $ \sa -> f (sa s1) (sa s2) (sa s3) (sa s4)
{-# INLINE zipsWith4 #-}

-- | Extract the higher order function that characterizes a 'Colens'.
--
-- The grate laws can be stated in terms or 'withColens':
--
-- Identity:
--
-- @
-- zipsWithF o runIdentity ≡ runIdentity
-- @
--
-- Composition:
--
-- @
-- zipsWithF o f . fmap (zipsWithF o g) ≡ zipsWithF o (f . fmap g . getCompose) . Compose
-- @
--
zipsWithF :: Functor f => AColens s t a b -> (f a -> b) -> f s -> t
zipsWithF o f s = cloneColensVl o f s
{-# INLINE zipsWithF #-}

-- | Use a 'Colens' to construct a 'Closure'.
--
closure :: Closed p => AColens s t a b -> p a b -> Closure p s t
closure o p = withColens o $ \sabt -> Closure (closed . grate sabt $ p)
{-# INLINE closure #-}

-- | Use a 'Colens' to construct an 'Environment'.
--
environment :: Closed p => AColens s t a b -> p a b -> Environment p s t
environment o p = withColens o $ \sabt -> Environment sabt p (curry eval)
{-# INLINE environment #-}

---------------------------------------------------------------------
-- MTL
---------------------------------------------------------------------

-- | Lift the current continuation into the calling context.
--
-- @
-- 'zipsWith' 'calledCC' :: 'MonadCont' m => (m b -> m b -> m s) -> s -> s -> m s
-- @
--
calledCC :: MonadCont m => Colens a (m a) (m b) (m a)
calledCC = grate callCC
{-# INLINE calledCC #-}

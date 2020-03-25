{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Lens (
    -- * Lens
    Lens
  , Lens'
  , Colens
  , Colens'
  , lens
  , lensVl
  , matching
  , cloneLens
  , cloneLensVl
  , colens
  , colensVl
  , comatching
  , cloneColens
    -- * Grate
  , Grate
  , Grate'
  , grate
  , grateVl
  , inverting
  , cloneGrate
  , cloneGrateVl
    -- * Optics
  , united
  , voided
  , represented
  , distributed
  , endomorphed
  , precomposed
  , dotted
  , continued
  , continuedT
  , calledCC
    -- * Operators
  , zipsWith0
  , zipsWith2
  , zipsWith3
  , zipsWith4 
  , zipsWithF
  , toPastro
  , toTambara
  , toClosure
  , toEnvironment
  , withLens
  , withColens
  , withGrate
    -- * Classes
  , Strong(..)
  , Costrong(..)
  , Closed(..)
) where

import Control.Monad.Cont
import Data.Distributive
import Data.Monoid (Endo(..))
import Data.Profunctor.Closed
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Iso
import Data.Profunctor.Optic.Types
import Data.Profunctor.Strong
import Data.Semimodule.Free
import qualified Data.Functor.Rep as F

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XTypeFamilies
-- >>> :set -XFlexibleContexts
-- >>> :set -XTupleSections
-- >>> import Control.Arrow
-- >>> import Control.Monad.Reader
-- >>> import Data.Int
-- >>> import Data.Complex
-- >>> import Data.Tuple (swap)
-- >>> import Data.Function ((&))
-- >>> import Data.List as L
-- >>> import Data.Monoid (Endo(..))
-- >>> :load Data.Profunctor.Optic

---------------------------------------------------------------------
-- 'Lens'
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
lensVl abst = dimap ((info &&& vals) . abst (flip Index id)) (uncurry id . swap) . first'
{-# INLINE lensVl #-}

-- | Obtain a 'Lens' from its free tensor representation.
--
matching :: (s -> (c , a)) -> ((c , b) -> t) -> Lens s t a b
matching sca cbt = dimap sca cbt . second'

-- | TODO: Document
--
cloneLens :: ALens s t a b -> Lens s t a b
cloneLens o = withLens o lens 

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
colens bsa bt = unsecond . dimap (uncurry bsa) (id &&& bt)

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
colensVl o = unfirst . dimap (uncurry id . swap) ((info &&& vals) . o (flip Index id))

-- | Obtain a 'Colens' from its free tensor representation.
--
-- >>> fib = comatching (uncurry L.take . swap) (id &&& L.reverse) --fib :: Colens Int [Int] [Int] [Int]
-- >>> 10 & fib ..~ \xs -> 1 : 1 : Prelude.zipWith (+) xs (Prelude.tail xs)
-- [89,55,34,21,13,8,5,3,2,1,1]
--
comatching :: ((c , s) -> a) -> (b -> (c , t)) -> Colens s t a b
comatching csa bct = unsecond . dimap csa bct

-- | TODO: Document
--
cloneColens :: AColens s t a b -> Colens s t a b
cloneColens o = withColens o colens 

---------------------------------------------------------------------
-- 'Grate'
---------------------------------------------------------------------

-- | Obtain a 'Grate' from a nested continuation.
--
-- The resulting optic is the corepresentable counterpart to 'Lens', 
-- and sits between 'Iso' and 'Setter'.
--
-- A 'Grate' lets you lift a profunctor through any representable 
-- functor (aka Naperian container). In the special case where the 
-- indexing type is finitary (e.g. 'Bool') then the tabulated type is 
-- isomorphic to a fied length vector (e.g. 'V2 a').
--
-- The identity container is representable, and representable functors 
-- are closed under composition.
--
-- See <https://www.cs.ox.ac.uk/jeremy.gibbons/publications/proyo.pdf>
-- section 4.6 for more background on 'Grate's, and compare to the 
-- /lens-family/ <http://hackage.haskell.org/package/lens-family-2.0.0/docs/Lens-Family2.html#t:Grate version>.
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
grate :: (((s -> a) -> b) -> t) -> Grate s t a b
grate sabt = dimap (flip ($)) sabt . closed

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
grateVl :: (forall f. Functor f => (f a -> b) -> f s -> t) -> Grate s t a b 
grateVl o = dimap (curry eval) ((o trivial) . Coindex) . closed

-- | Construct a 'Grate' from a pair of inverses.
--
inverting :: (s -> a) -> (b -> t) -> Grate s t a b
inverting sa bt = grate $ \sab -> bt (sab sa)

-- | TODO: Document
--
cloneGrate :: AGrate s t a b -> Grate s t a b
cloneGrate k = withGrate k grate

-- | Extract the higher order function that characterizes a 'Grate'.
--
-- The grate laws can be stated in terms or 'withGrate':
-- 
-- Identity:
-- 
-- @
-- cloneGrateVl o runIdentity ≡ runIdentity
-- @
-- 
-- Composition:
-- 
-- @ 
-- cloneGrateVl o f . fmap (cloneGrateVl o g) ≡ cloneGrateVl o (f . fmap g . getCompose) . Compose
-- @
--
cloneGrateVl :: AGrate s t a b -> (forall f . Functor f => (f a -> b) -> f s -> t)
cloneGrateVl o ab s = withGrate o $ \sabt -> sabt $ \get -> ab (fmap get s)
{-# INLINE cloneGrateVl #-}

---------------------------------------------------------------------
-- Optics 
---------------------------------------------------------------------

-- | There is a '()' in everything.
--
-- >>> "hello" ^. united
-- ()
-- >>> "hello" & united .~ ()
-- "hello"
--
united :: Lens' a ()
united = lens (const ()) const

-- | There is everything in a 'Void'.
--
-- >>> Nothing & fmapped . voided ..~ abs
-- Nothing
--
voided :: Lens' Void a
voided = lens absurd const

-- | Obtain a 'Grate' from a 'F.Representable' functor.
--
represented :: F.Representable f => Grate (f a) (f b) a b
represented = tabulated . closed
{-# INLINE represented #-}

-- | Obtain a 'Grate' from a distributive functor.
--
distributed :: Distributive f => Grate (f a) (f b) a b
distributed = grate (`cotraverse` id)
{-# INLINE distributed #-}

-- | Obtain a 'Grate' from an endomorphism. 
--
-- >>> flip appEndo 2 $ zipsWith2 endomorphed (+) (Endo (*3)) (Endo (*4))
-- 14
--
endomorphed :: Grate' (Endo a) a
endomorphed = dimap appEndo Endo . closed
{-# INLINE endomorphed #-}

-- | Obtain a 'Grate' from a linear map.
--
precomposed :: Grate (Lin a b1 c) (Lin a b2 c) (Vec a b1) (Vec a b2)
precomposed = dimap runLin Lin . closed . dimap Vec runVec
{-# INLINE precomposed #-}

-- | Obtain a 'Grate' from a linear functional.
--
dotted :: Grate c (Cov a c) a a
dotted = grate Cov
{-# INLINE dotted #-}

-- | Obtain a 'Grate' from a continuation.
--
-- @
-- 'zipsWith2' 'continued' :: (a -> a -> a) -> c -> c -> 'Cont' a c
-- @
--
continued :: Grate c (Cont a c) a a
continued = grate cont
{-# INLINE continued #-}

-- | Obtain a 'Grate' from a continuation.
--
-- @
-- 'zipsWith2' 'continued' :: (m a -> m a -> m a) -> c -> c -> 'ContT' a m c 
-- @
--
continuedT :: Grate c (ContT a m c) (m a) (m a)
continuedT = grate ContT
{-# INLINE continuedT #-}

-- | Lift the current continuation into the calling context.
--
-- @
-- 'zipsWith2' 'calledCC' :: 'MonadCont' m => (m b -> m b -> m s) -> s -> s -> m s
-- @
--
calledCC :: MonadCont m => Grate a (m a) (m b) (m a)
calledCC = grate callCC
{-# INLINE calledCC #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Set all fields to the given value.
--
-- This is essentially a restricted variant of 'Data.Profunctor.Optic.View.review'.
--
zipsWith0 :: AGrate s t a b -> b -> t
zipsWith0 o b = withGrate o $ \sabt -> sabt (const b)
{-# INLINE zipsWith0 #-}

-- | Zip over a 'Grate'. 
--
-- @\\f -> 'zipsWith2' 'closed' ('zipsWith2' 'closed' f) ≡ 'zipsWith2' ('closed' . 'closed')@
--
zipsWith2 :: AGrate s t a b -> (a -> a -> b) -> s -> s -> t
zipsWith2 o aab s1 s2 = withGrate o $ \sabt -> sabt $ \get -> aab (get s1) (get s2)
{-# INLINE zipsWith2 #-}

-- | Zip over a 'Grate' with 3 arguments.
--
zipsWith3 :: AGrate s t a b -> (a -> a -> a -> b) -> (s -> s -> s -> t)
zipsWith3 o aaab s1 s2 s3 = withGrate o $ \sabt -> sabt $ \sa -> aaab (sa s1) (sa s2) (sa s3)
{-# INLINE zipsWith3 #-}

-- | Zip over a 'Grate' with 4 arguments.
--
zipsWith4 :: AGrate s t a b -> (a -> a -> a -> a -> b) -> (s -> s -> s -> s -> t)
zipsWith4 o aaaab s1 s2 s3 s4 = withGrate o $ \sabt -> sabt $ \sa -> aaaab (sa s1) (sa s2) (sa s3) (sa s4)
{-# INLINE zipsWith4 #-}

-- | Extract the higher order function that characterizes a 'Grate'.
--
-- The grate laws can be stated in terms or 'withGrate':
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
zipsWithF :: Functor f => AGrate s t a b -> (f a -> b) -> f s -> t
zipsWithF = cloneGrateVl
{-# INLINE zipsWithF #-}

-- | Use a 'Lens' to construct a 'Pastro'.
--
toPastro :: ALens s t a b -> p a b -> Pastro p s t
toPastro o p = withLens o $ \sa sbt -> Pastro (uncurry sbt . swap) p (\s -> (sa s, s))

-- | Use a 'Lens' to construct a 'Tambara'.
--
toTambara :: Strong p => ALens s t a b -> p a b -> Tambara p s t
toTambara o p = withLens o $ \sa sbt -> Tambara (first' . lens sa sbt $ p)

-- | Use a 'Grate' to construct a 'Closure'.
--
toClosure :: Closed p => AGrate s t a b -> p a b -> Closure p s t
toClosure o p = withGrate o $ \sabt -> Closure (closed . grate sabt $ p)
{-# INLINE toClosure #-}

-- | Use a 'Grate' to construct an 'Environment'.
--
toEnvironment :: Closed p => AGrate s t a b -> p a b -> Environment p s t
toEnvironment o p = withGrate o $ \sabt -> Environment sabt p (curry eval)
{-# INLINE toEnvironment #-}

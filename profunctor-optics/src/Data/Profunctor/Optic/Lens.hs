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
  , inside
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
  , first
  , second
  , cofirst
  , cosecond
  , contained
  , represented
  , distributed
  , endomorphed
  , continued
  , continuedT
  , calledCC
    -- * Operators
  , ozips
  , coview
  , zipsWith
  , zipsWith3
  , zipsWith4 
  , zipsWithF
  , ozipsWith
  , intersectsMap
  , differencesMap
  , intersectsWithMap
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
import Data.Containers as C hiding (unions)
import Data.Distributive
import Data.MonoTraversable (Element)
import Data.Monoid (Endo(..))
import Data.Profunctor.Closed
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Iso
import Data.Profunctor.Optic.Types
import Data.Profunctor.Strong
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
-- >>> import qualified Data.ByteString as B
-- >>> import qualified Data.ByteString.Char8 as C
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
inside l = lensVl $ \f es -> o es <$> f (i es) where
  i es = cotabulate $ \ e -> info $ cloneLensVl l sell (cosieve es e)
  o es ea = cotabulate $ \ e -> flip vals (cosieve ea e) $ cloneLensVl l sell (cosieve es e)
  sell x = Index x id
{-# INLINE inside #-}

--coinside :: Representable p => AGrate s t a b -> Grate (p e s) (p e t) (p e a) (p e b)

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
{-# INLINE united #-}

-- | There is everything in a 'Void'.
--
-- >>> Nothing & fmapped . voided ..~ abs
-- Nothing
--
voided :: Lens' Void a
voided = lens absurd const
{-# INLINE voided #-}

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
cofirst :: Colens a b (a, c) (b, c) 
cofirst = unfirst
{-# INLINE cofirst #-}

-- | TODO: Document
--
cosecond :: Colens a b (c, a) (c, b) 
cosecond = unsecond
{-# INLINE cosecond #-}

-- | TODO: Document
--
contained :: IsSet s => Element s -> Lens' s Bool
contained k = lens (C.member k) $ \s b -> if b then C.insertSet k s else C.deleteSet k s
{-# INLINE contained #-}

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
-- >>> flip appEndo 2 $ zipsWith endomorphed (+) (Endo (*3)) (Endo (*4))
-- 14
--
endomorphed :: Grate' (Endo a) a
endomorphed = dimap appEndo Endo . closed
{-# INLINE endomorphed #-}

-- | Obtain a 'Grate' from a continuation.
--
-- @
-- 'zipsWith' 'continued' :: (a -> a -> a) -> c -> c -> 'Cont' a c
-- @
--
continued :: Grate c (Cont a c) a a
continued = grate cont
{-# INLINE continued #-}

-- | Obtain a 'Grate' from a continuation.
--
-- @
-- 'zipsWith' 'continued' :: (m a -> m a -> m a) -> c -> c -> 'ContT' a m c 
-- @
--
continuedT :: Grate c (ContT a m c) (m a) (m a)
continuedT = grate ContT
{-# INLINE continuedT #-}

-- | Lift the current continuation into the calling context.
--
-- @
-- 'zipsWith' 'calledCC' :: 'MonadCont' m => (m b -> m b -> m s) -> s -> s -> m s
-- @
--
calledCC :: MonadCont m => Grate a (m a) (m b) (m a)
calledCC = grate callCC
{-# INLINE calledCC #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Zip over a mono 'Grate'. 
--
-- >>> ozips closed C.reverse id $ C.pack "foo"
-- [(111,102),(111,111),(102,111)]
--
ozips :: MonoZip a => AGrate s t a [(Element a, Element a)] -> s -> s -> t
ozips o = zipsWith o ozip
{-# INLINE ozips #-}

-- | Set all fields to the given value.
--
-- Compare 'Data.Profunctor.Optic.View.review'.
--
coview :: AGrate s t a b -> b -> t
coview o b = withGrate o $ \sabt -> sabt (const b)
{-# INLINE coview #-}

-- | Zip over a 'Grate'. 
--
-- @\\f -> 'zipsWith' 'closed' ('zipsWith' 'closed' f) ≡ 'zipsWith' ('closed' . 'closed')@
--
zipsWith :: AGrate s t a b -> (a -> a -> b) -> s -> s -> t
zipsWith o f s1 s2 = withGrate o $ \sabt -> sabt $ \sa -> f (sa s1) (sa s2)
{-# INLINE zipsWith #-}

-- | Zip over a 'Grate' with 3 arguments.
--
zipsWith3 :: AGrate s t a b -> (a -> a -> a -> b) -> (s -> s -> s -> t)
zipsWith3 o f s1 s2 s3 = withGrate o $ \sabt -> sabt $ \sa -> f (sa s1) (sa s2) (sa s3)
{-# INLINE zipsWith3 #-}

-- | Zip over a 'Grate' with 4 arguments.
--
zipsWith4 :: AGrate s t a b -> (a -> a -> a -> a -> b) -> (s -> s -> s -> s -> t)
zipsWith4 o f s1 s2 s3 s4 = withGrate o $ \sabt -> sabt $ \sa -> f (sa s1) (sa s2) (sa s3) (sa s4)
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

-- | Zip over a mono 'Grate'. 
--
-- >>> ozipsWith closed (+) B.pack B.pack [1..3]
-- "\STX\EOT\ACK"
--
ozipsWith :: MonoZip a => AGrate s t a a -> (Element a -> Element a -> Element a) -> s -> s -> t
ozipsWith o f s1 s2 = withGrate o $ \sabt -> sabt $ \sa -> ozipWith f (sa s1) (sa s2)
{-# INLINE ozipsWith #-}

-- | TODO: Document
--
intersectsMap :: PolyMap m => AGrate s t (m a) (m a) -> s -> s -> t
intersectsMap o = zipsWith o C.intersectionMap
{-# INLINE intersectsMap #-}

-- | TODO: Document
--
differencesMap :: PolyMap m => AGrate s t (m a) (m a) -> s -> s -> t
differencesMap o = zipsWith o C.differenceMap
{-# INLINE differencesMap #-}

-- | TODO: Document
--
intersectsWithMap :: PolyMap m => AGrate s t (m a) (m b) -> (a -> a -> b) -> s -> s -> t
intersectsWithMap o f s1 s2 = withGrate o $ \sabt -> sabt $ \sa -> C.intersectionWithMap f (sa s1) (sa s2)
{-# INLINE intersectsWithMap #-}

-- | Use a 'Lens' to construct a 'Pastro'.
--
toPastro :: ALens s t a b -> p a b -> Pastro p s t
toPastro o p = withLens o $ \sa sbt -> Pastro (uncurry sbt . swap) p (\s -> (sa s, s))
{-# INLINE toPastro #-}

-- | Use a 'Lens' to construct a 'Tambara'.
--
toTambara :: Strong p => ALens s t a b -> p a b -> Tambara p s t
toTambara o p = withLens o $ \sa sbt -> Tambara (first' . lens sa sbt $ p)
{-# INLINE toTambara #-}

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

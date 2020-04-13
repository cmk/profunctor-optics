{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -fno-warn-duplicate-exports #-}
module Data.Profunctor.Optic.Lens (
    -- * Lens
    Lens
  , Lens'
  , Colens
  , Colens'
  , lens
  , lensVl
  , colens
  , relens
  , colensVl
  , relensVl
  , matching
  , inverting
  , comatching
  , cloneLens
  , cloneLensVl
  , cloneColens
  , cloneColensVl
  , inside
  , toPastro
  , toTambara
  , toClosure
  , toEnvironment
    -- * Optics
  , first
  , cofirst
  , second
  , cosecond
  , closed
  , united
  , voided
  , distributed
  , morphed
  , continued
  , continuedT
  , calledCC
  , unlifted
  , masked
    -- * Operators
  , coview
  , zipsWith2
  , zipsWith3
  , zipsWith4 
  , zipsWithF
    -- * Classes
  , Strong(..)
  , Closed(..)
) where

import Control.Monad.Cont
import Control.Monad.IO.Unlift
import Data.Distributive
import Data.Monoid (Endo(..))
import Data.Profunctor.Closed
import Data.Profunctor.Rep (unfirstCorep, unsecondCorep)
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Iso
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Combinator 
import Data.Profunctor.Strong
import qualified Control.Exception as Ex

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
-- Compare 'Data.Profunctor.Optic.Lens.colensVl' and 'Data.Profunctor.Optic.Traversal.traversalVl'.
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

-- | Obtain a 'Colens' from a nested continuation.
--
-- The resulting optic is the corepresentable counterpart to 'Lens', 
-- and sits between 'Iso' and 'Setter'.
--
-- A 'Colens' lets you lift a profunctor through any representable 
-- functor (aka Naperian container). In the special case where the 
-- indexing type is finitary (e.g. 'Bool') then the tabulated type is 
-- isomorphic to a fied length vector (e.g. 'V2 a').
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
colens :: (((s -> a) -> b) -> t) -> Colens s t a b
colens f = dimap (flip ($)) f . closed
{-# INLINE colens #-}

-- | Obtain a 'Colens' from a getter and setter. 
--
-- @
-- 'relens' f g ≡ \\f g -> 're' ('lens' f g)
-- 'relens' bsia bt ≡ 'relensVl' '$' \\ts b -> bsia b '<$>' (ts . bt '$' b)
-- 'review' $ 'relens' f g ≡ f
-- 'set' . 're' $ 're' ('lens' f g) ≡ g
-- @
--
-- /Caution/: This function is inherently recursive, similar to < http://hackage.haskell.org/package/base-4.12.0.0/docs/Control-Arrow.html#t:ArrowLoop ArrowLoop >. 
-- In addition to the normal optic laws, the input functions must have 
-- the correct < https://wiki.haskell.org/Lazy_pattern_match laziness > annotations.
--
-- For example, this is a perfectly valid 'Colens':
--
-- @
-- ct21 :: Colens a b (a, c) (b, c)
-- ct21 = flip relens fst $ \ ~(_,c) b -> (b,c)
-- @
--
-- However removing the annotation will result in a faulty optic.
-- 
-- See 'Data.Profunctor.Optic.Property'.
--
relens :: (b -> s -> a) -> (b -> t) -> Colens s t a b
relens bsa bt = cosecond . dimap (uncurry bsa) (id &&& bt)

-- | Transform a Van Laarhoven colens into a profunctor colens.
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
colensVl :: (forall f. Functor f => (f a -> b) -> f s -> t) -> Colens s t a b 
colensVl o = dimap (curry eval) ((o trivial) . Coindex) . closed
{-# INLINE colensVl #-}

-- | Transform a Van Laarhoven relens into a profunctor relens.
--
-- Compare 'colensVl'.
--
-- /Caution/: In addition to the normal optic laws, the input functions
-- must have the correct laziness annotations.
--
-- For example, this is a perfectly valid 'Colens':
--
-- @
-- ct21 :: Colens a b (a, c) (b, c)
-- ct21 = relensVl $ \f ~(a,b) -> (,b) <$> f a
-- @
--
-- However removing the annotation will result in a faulty optic.
-- 
-- @since 0.0.3
relensVl :: (forall f. Functor f => (t -> f s) -> b -> f a) -> Colens s t a b
relensVl o = cofirst . dimap (uncurry id . swap) ((info &&& vals) . o (flip Index id))

-- | Obtain a 'Lens' from its free tensor representation.
--
matching :: (s -> (c , a)) -> ((c , b) -> t) -> Lens s t a b
matching sca cbt = dimap sca cbt . second'

-- | Construct a 'Colens' from a pair of inverses.
--
inverting :: (s -> a) -> (b -> t) -> Colens s t a b
inverting sa bt = colens $ \sab -> bt (sab sa)
{-# INLINE inverting #-}

-- | Obtain a 'Colens' from its free tensor representation.
--
-- >>> fib = comatching (uncurry L.take . swap) (id &&& L.reverse) --fib :: Colens Int [Int] [Int] [Int]
-- >>> 10 & fib ..~ \xs -> 1 : 1 : Prelude.zipWith (+) xs (Prelude.tail xs)
-- [89,55,34,21,13,8,5,3,2,1,1]
--
comatching :: ((c , s) -> a) -> (b -> (c , t)) -> Colens s t a b
comatching csa bct = cosecond . dimap csa bct

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

-- | TODO: Document
--
cloneColens :: AColens s t a b -> Colens s t a b
cloneColens k = withColens k colens
{-# INLINE cloneColens #-}

-- | Extract the higher order function that characterizes a 'Colens'.
--
-- The colens laws can be stated in terms or 'withColens':
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

-- | Use a 'Colens' to construct a 'Closure'.
--
toClosure :: Closed p => AColens s t a b -> p a b -> Closure p s t
toClosure o p = withColens o $ \sabt -> Closure (closed . colens sabt $ p)
{-# INLINE toClosure #-}

-- | Use a 'Colens' to construct an 'Environment'.
--
toEnvironment :: Closed p => AColens s t a b -> p a b -> Environment p s t
toEnvironment o p = withColens o $ \sabt -> Environment sabt p (curry eval)
{-# INLINE toEnvironment #-}

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
cofirst :: Colens a b (a, c) (b, c) 
cofirst = cloneColens unfirstCorep
{-# INLINE cofirst #-}

-- | TODO: Document
--
second :: Lens (c, a) (c, b) a b
second = second'
{-# INLINE second #-}

-- | TODO: Document
--
cosecond :: Colens a b (c, a) (c, b)
cosecond = cloneColens unsecondCorep
{-# INLINE cosecond #-}

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

-- | Obtain a 'Colens' from a distributive functor.
--
distributed :: Distributive f => Colens (f a) (f b) a b
distributed = colens (\f -> fmap f . distribute $ id)
{-# INLINE distributed #-}

-- | Obtain a 'Colens' from an endomorphism. 
--
-- >>> flip appEndo 2 $ zipsWith morphed (+) (Endo (*3)) (Endo (*4))
-- 14
--
morphed :: Colens' (Endo a) a
morphed = dimap appEndo Endo . closed
{-# INLINE morphed #-}

-- | Obtain a 'Colens' from a continuation.
--
-- @
-- 'zipsWith' 'continued' :: (a -> a -> a) -> c -> c -> 'Cont' a c
-- @
--
continued :: Colens c (Cont a c) a a
continued = colens cont
{-# INLINE continued #-}

-- | Obtain a 'Colens' from a continuation.
--
-- @
-- 'zipsWith' 'continued' :: (m a -> m a -> m a) -> c -> c -> 'ContT' a m c 
-- @
--
continuedT :: Colens c (ContT a m c) (m a) (m a)
continuedT = colens ContT
{-# INLINE continuedT #-}

-- | Lift the current continuation into the calling context.
--
-- @
-- 'zipsWith' 'calledCC' :: 'MonadCont' m => (m b -> m b -> m s) -> s -> s -> m s
-- @
--
calledCC :: MonadCont m => Colens a (m a) (m b) (m a)
calledCC = colens callCC
{-# INLINE calledCC #-}

-- | Unlift an action into an 'IO' context.
--
-- @
-- 'liftIO' ≡ 'coview' 'unlifted'
-- @
--
-- >>> let catchA = catch @ArithException
-- >>> zipsWith unlifted (flip catchA . const) (throwIO Overflow) (print "caught") 
-- "caught" 
--
unlifted :: MonadUnliftIO m => Colens (m a) (m b) (IO a) (IO b)
unlifted = colens withRunInIO
{-# INLINE unlifted #-}

-- | Mask actions in an unlifted context.
--
masked :: MonadUnliftIO m => Colens (m a) (m b) (m a) (m b)
masked = colens $ \f -> withRunInIO $ \run -> 
  Ex.mask $ \unmask -> run $ f $ liftIO . unmask . run
{-# INLINE masked #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Set all fields to the given value.
--
-- Compare 'Data.Profunctor.Optic.View.review'.
--
coview :: AColens s t a b -> b -> t
coview o b = withColens o $ \sabt -> sabt (const b)
{-# INLINE coview #-}

-- | Zip over a 'Colens'. 
--
-- @\\f -> 'zipsWith' 'closed' ('zipsWith' 'closed' f) ≡ 'zipsWith' ('closed' . 'closed')@
--
zipsWith2 :: AColens s t a b -> (a -> a -> b) -> s -> s -> t
zipsWith2 o f s1 s2 = withColens o $ \sabt -> sabt $ \sa -> f (sa s1) (sa s2)
{-# INLINE zipsWith2 #-}

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
-- The colens laws can be stated in terms or 'withColens':
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
zipsWithF = cloneColensVl
{-# INLINE zipsWithF #-}

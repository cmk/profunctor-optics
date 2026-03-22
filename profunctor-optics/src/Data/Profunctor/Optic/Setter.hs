{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Setter (
    -- * Setter
    Setter
  , Setter'
  , Cosetter
  , Cosetter'
  , setter
  , ixsetter
  , closing
  , cosetter
    -- * Setter1
  , Setter1
  , Setter1'
  , Cosetter1
  , Cosetter1'
  , setter1
  , cosetter1
    -- * Optics
  , cod
  , dom
  , fmapped
  , imappedRep
  , contramapped
  , liftedM
  , liftedA
  , reliftedA
  , reliftedF
  , zipListed
  , forwarded
  , censored
  , zipped
  , modded
  , cond
    -- * Operators
  , over
  , ixover
  , cxover
  , set
  , sets
  , ixset
  , ixsets
  , coset
  , cosets
  , cxset
  , cxsets
    -- * mtl
  , assigns
  , modifies
  , locally
  , scribe
) where

import Control.Applicative (liftA,ZipList(..))
import Control.Monad.Reader as Reader
import Control.Monad.State as State
import Control.Monad.Writer as Writer
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Import hiding ((&&&))
import Data.Profunctor.Optic.Combinator
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Iso (sieved,cosieved)
import Data.Profunctor.Optic.Traversal
import qualified Data.Functor.Rep as F

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> :set -XRankNTypes
-- >>> import Control.Category ((>>>))
-- >>> import Control.Arrow (Kleisli(..))
-- >>> import Control.Monad.State
-- >>> import Control.Monad.Reader
-- >>> import Control.Monad.Writer
-- >>> import Data.Bool (bool)
-- >>> import Data.Complex
-- >>> import Data.Function ((&))
-- >>> import Data.Functor.Rep
-- >>> import Data.Functor.Identity
-- >>> import Data.Functor.Contravariant
-- >>> import Data.Semigroup
-- >>> import Data.Tuple (swap)
-- >>> :load Data.Profunctor.Optic
-- >>> import Prelude

---------------------------------------------------------------------
-- Setter
---------------------------------------------------------------------

-- | Obtain a 'Setter' from a <http://conal.net/blog/posts/semantic-editor-combinators SEC>.
--
-- To demote an optic to a semantic edit combinator, use the section @(l ..~)@ or @over l@.
--
-- >>> [("The",0),("quick",1),("brown",1),("fox",2)] & setter fmap . first' ..~ Prelude.length
-- [(3,0),(5,1),(5,1),(3,2)]
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input function satisfies the following
-- properties:
--
-- * @abst id ≡ id@
--
-- * @abst f . abst g ≡ abst (f . g)@
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
setter :: ((a -> b) -> s -> t) -> Setter s t a b
setter abst = sieved abst . represent (\f -> distribute . fmap f)
{-# INLINE setter #-}

-- | Build an 'Ixsetter' from an indexed function.
--
-- @
-- 'ixsetter' '.' 'ixsets' ≡ 'id'
-- 'ixsets' '.' 'ixsetter' ≡ 'id'
-- @
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @iabst (const id) ≡ id@
--
-- * @fmap (iabst $ const f) . (iabst $ const g) ≡ iabst (const $ f . g)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
-- @since 0.0.3
ixsetter :: ((i -> a -> b) -> s -> t) -> Ixsetter i s t a b
ixsetter f = setter $ \iab -> f (curry iab) . snd 
{-# INLINE ixsetter #-}

-- | Every valid 'Colens' is a 'Setter'.
--
closing :: (((s -> a) -> b) -> t) -> Setter s t a b
closing sabt = setter $ \ab s -> sabt $ \sa -> ab (sa s)
{-# INLINE closing #-}

-- | Obtain a 'Cosetter' from a <http://conal.net/blog/posts/semantic-editor-combinators SEC>.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input function satisfies the following
-- properties:
--
-- * @abst id ≡ id@
--
-- * @abst f . abst g ≡ abst (f . g)@
--
cosetter :: ((a -> t) -> s -> t) -> Cosetter s t a t
cosetter abst = cosieved abst . corepresent (\f -> fmap f . sequenceA)
{-# INLINE cosetter #-}

---------------------------------------------------------------------
-- Setter1
---------------------------------------------------------------------

-- | TODO: Document
--
-- @since 0.0.3
setter1 :: ((a -> b) -> a -> t) -> Setter1 a t a b
setter1 abst = sieved abst . represent (\f -> distribute1 . fmap f)
{-# INLINE setter1 #-}

-- | TODO: Document
--
-- @since 0.0.3
cosetter1 :: ((a -> t) -> s -> t) -> Cosetter1 s t a t
cosetter1 abst = cosieved abst . corepresent (\f -> fmap f . sequence1)
{-# INLINE cosetter1 #-}

---------------------------------------------------------------------
-- Optics 
---------------------------------------------------------------------

-- | Map covariantly over the output of a profunctor.
--
-- The most common profunctor to use this with is @(->)@.
--
-- @
-- (dom ..~ f) g x ≡ f (g x)
-- cod @(->) ≡ 'Data.Profunctor.Optic.Lens.withColens' 'Data.Profunctor.Closed.closed' 'Data.Profunctor.Optic.Setter.closing'
-- @
--
-- >>> (cod ..~ show) length [1,2,3]
-- "3"
--
cod :: Profunctor p => Setter (p r a) (p r b) a b
cod = setter rmap
{-# INLINE cod #-}

-- | Map contravariantly over the input of a profunctor.
--
-- The most common profunctor to use this with is @(->)@.
--
-- @
-- ('dom' '..~' f) g x ≡ g (f x)
-- @
--
-- >>> (dom ..~ show) length [1,2,3]
-- 7
--
dom :: Profunctor p => Setter (p b r) (p a r) a b
dom = setter lmap
{-# INLINE dom #-}

-- | 'Setter' on each value of a functor.
--
fmapped :: Functor f => Setter (f a) (f b) a b
fmapped = setter fmap
{-# INLINE fmapped #-}

-- | 'Ixsetter' on each value of a representable functor.
--
-- >>> 1 :+ 2 & ixany imappedRep %~ bool 20 10 . getAny
-- 20 :+ 10
--
imappedRep :: F.Representable f => Ixsetter (F.Rep f) (f a) (f b) a b
imappedRep = ixsetter F.imapRep
{-# INLINE imappedRep #-}

-- | 'Setter' on each value of a contravariant functor.
--
-- @
-- 'Data.Functor.Contravariant.contramap' ≡ 'over' 'contramapped'
-- @
--
-- >>> getPredicate (over contramapped (*2) (Predicate even)) 5
-- True
-- >>> getOp (over contramapped (*5) (Op show)) 100
-- "500"
--
contramapped :: Contravariant f => Setter (f b) (f a) a b
contramapped = setter contramap
{-# INLINE contramapped #-}

-- | 'Setter' on each value of a monad.
--
liftedM :: Monad m => Setter (m a) (m b) a b
liftedM = setter liftM
{-# INLINE liftedM #-}

-- | 'Setter' on each value of an applicative.
--
-- @
-- 'Control.Applicative.liftA' ≡ 'setter' 'liftedA'
-- @
--
-- >>> setter liftedA Identity [1,2,3]
-- [Identity 1,Identity 2,Identity 3]
-- >>> set liftedA 2 (Just 1)
-- Just 2
--
liftedA :: Applicative f => Setter (f a) (f b) a b
liftedA = setter liftA
{-# INLINE liftedA #-}

-- | TODO: Document
--
reliftedA :: Applicative f => Cosetter (f a) (f b) a b
reliftedA p = cotabulate $ fmap (cosieve p) . sequenceA
{-# INLINE reliftedA #-}

-- | TODO: Document
--
-- @since 0.0.3
reliftedF :: Apply f => Cosetter1 (f a) (f b) a b
reliftedF p = cotabulate $ fmap (cosieve p) . sequence1
{-# INLINE reliftedF #-}

-- | Variant of 'reliftedA' specialized to zip-toListOf.
--
-- Useful because toListOf are not 'Control.Coapplicative.Coapplicative'.
--
-- @since 0.0.3
zipListed :: Cosetter [a] [b] a b
zipListed = dimap ZipList getZipList . reliftedA
{-# INLINE zipListed #-}

-- | 'Setter' on the local environment of a 'Reader'. 
--
-- Use to lift reader actions into a larger environment:
--
-- >>> runReader (ask & forwarded ..~ fst) (1,2)
-- 1
--
forwarded :: Setter (ReaderT r2 m a) (ReaderT r1 m a) r1 r2
forwarded = setter withReaderT
{-# INLINE forwarded #-}

-- | TODO: Document
--
censored :: Writer.MonadWriter w m => Setter' (m a) w
censored = setter Writer.censor
{-# INLINE censored #-}

-- | 'Setter' on the codomain of a zipping function.
--
-- >>> ((,) & zipped ..~ swap) 1 2
-- (2,1)
--
zipped :: Setter (u -> v -> a) (u -> v -> b) a b
zipped = setter ((.)(.)(.))
{-# INLINE zipped #-}

-- | TODO: Document
--
modded :: (a -> Bool) -> Setter' (a -> b) b
modded p = setter $ \mods f a -> if p a then mods (f a) else f a
{-# INLINE modded #-}

-- | Apply a function only when the given condition holds.
--
-- See also 'Data.Profunctor.Optic.Traversal0.predicated' & 'Data.Profunctor.Optic.Prism.filtered'.
--
cond :: (a -> Bool) -> Setter' a a
cond p = setter $ \f a -> if p a then f a else a
{-# INLINE cond #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Set the focus of a 'Setter'.
--
-- @ 
-- 'set' o y ('set' o x a) ≡ 'set' o y a
-- 'set' o b = 'Data.Functor.runIdentity' . (o *~ 'Data.Functor.Identity' b)
-- @
--
set :: ASetter s t a b -> b -> s -> t
set o b = sets o $ const b
{-# INLINE set #-}

-- | Set the focus of a 'Setter'.
--
sets ::  ASetter s t a b -> (a -> b) -> s -> t
sets o = (runIdentity #.) #. traverseOf o .# (Identity #.)
{-# INLINE sets #-}

-- | Set the focus of a 'Ixsetter'.
--
-- Equivalent to 'ixsets' with the current value ignored.
--
-- @
-- 'set' o ≡ 'ixset' o '.' 'const'
-- @
--
-- @since 0.0.3
ixset :: Monoid i => AIxsetter i s t a b -> (i -> b) -> s -> t
ixset o = ixsets o . (const .)
{-# INLINE ixset #-}

-- | Set the focus of a 'Ixsetter'.
--
-- @since 0.0.3
ixsets :: Monoid i => AIxsetter i s t a b -> (i -> a -> b) -> s -> t
ixsets o f = curry (sets o $ uncurry f) mempty
{-# INLINE ixsets #-}

-- | Set the focus of a 'Cosetter'.
--
-- @
-- 'coset' o b = (o '/~' b) . 'Data.Functor.Identity'
-- @
--
coset :: ACosetter s t a b -> b -> s -> t
coset o b = cosets o $ const b

-- | Set the focus of a 'Cosetter'.
--
cosets :: ACosetter s t a b -> (a -> b) -> s -> t
cosets o = (.# Identity) #. cotraverseOf o .# (.# runIdentity) 
{-# INLINE cosets #-}

-- | Set the focus of a 'Cxsetter'.
--
-- Equivalent to 'cxsets' with the current value ignored.
--
-- @since 0.0.3
cxset :: Monoid i => ACxsetter i s t a b -> (i -> b) -> s -> t 
cxset o ib = cxsets o $ flip (const ib)
{-# INLINE cxset #-}

-- | Set the focus of a 'Cxsetter'.
--
-- @since 0.0.3
cxsets :: Monoid i => ACxsetter i s t a b -> (i -> a -> b) -> s -> t 
cxsets o f = flip (cosets o $ flip f) mempty
{-# INLINE cxsets #-}

---------------------------------------------------------------------
-- Mtl
---------------------------------------------------------------------

-- | Replace the target(s) of a settable in a monadic state.
--
assigns :: MonadState s m => Optic (->) s s a b -> b -> m ()
assigns o b = State.modify (o (const b))
{-# INLINE assigns #-}

-- | Map over the target(s) of a 'Setter' in a monadic state.
--
modifies :: MonadState s m => Optic (->) s s a b -> (a -> b) -> m ()
modifies o f = State.modify (o f)
{-# INLINE modifies #-}

-- | Modify the value of a 'Reader' environment.
--
-- @
-- 'locally' l 'id' a ≡ a
-- 'locally' l f '.' locally l g ≡ 'locally' l (f '.' g)
-- @
--
-- >>> (1,1) & locally first' (+1) (uncurry (+))
-- 3
-- >>> "," & locally (setter ($)) ("Hello" <>) (<> " world!")
-- "Hello, world!"
--
-- Compare 'forwarded'.
--
locally :: MonadReader s m => Optic (->) s s a b -> (a -> b) -> m r -> m r
locally o f = Reader.local (o f)
{-# INLINE locally #-}

-- | Write to a fragment of a larger 'Writer' format.
--
scribe :: MonadWriter w m => Monoid s => Optic (->) s w a b -> b -> m ()
scribe o b = Writer.tell (o (const b) mempty)
{-# INLINE scribe #-}

{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
module Data.Profunctor.Optic.Setter (
    -- * Constructors
    -- ** Setter, Ixsetter
    Setter, Setter'
  , Ixsetter, Ixsetter'
  , setter
  , ixsetter
  , closing
    -- ** Setter1, Ixsetter1
  , Setter1, Setter1'
  , Ixsetter1, Ixsetter1'
  , setter1
  , ixsetter1
    -- * Dual Constructors
    -- ** Cosetter, Cxsetter
  , Cosetter, Cosetter'
  , Cxsetter, Cxsetter'
  , cosetter
    -- ** Cosetter1, Cxsetter1
  , Cosetter1, Cosetter1'
  , Cxsetter1, Cxsetter1'
  , cosetter1
    -- * Optics
    -- ** Setter, Ixsetter
  , fmapped
  , contramapped
  , imappedRep
  , domain
  , codomain
  , liftedM
  , liftedA
  , forwarded
  , censored
  , zipped
  , modded
  , conditioned
    -- ** Setter1, Ixsetter1
    -- * Dual Optics
    -- ** Cosetter, Cxsetter
    -- ** Cosetter1, Cxsetter1
  , coliftedA
  , coliftedF
  , zipListed
    -- * Operators
    -- ** Setter, Ixsetter
  , set
  , ixset
  , sets
  , ixsets
  , over
  , ixover
    -- ** Setter1, Ixsetter1
    -- * Dual Operators
    -- ** Cosetter, Cxsetter
  , coset
  , cxset
  , cosets
  , cxsets
  , cxover
    -- ** Cosetter1, Cxsetter1
    -- * MTL
  , assigns
  , ixassigns
  , modifies
  , ixmodifies
  , localizes
  , tells
    -- * Re-exports
) where

import Control.Applicative (liftA,ZipList(..))
import Control.Monad.Reader as Reader
import Control.Monad.State as State
import Control.Monad.Writer as Writer
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Import hiding ((&&&))
import Data.Profunctor.Optic.Combinator
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Iso (indexing,coindexing)
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
-- Constructors
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
setter abst = indexing abst . representing (\f -> distribute . fmap f)
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

---------------------------------------------------------------------
-- Setter1
---------------------------------------------------------------------

-- | TODO: Document
--
-- @since 0.0.3
setter1 :: ((a -> b) -> a -> t) -> Setter1 a t a b
setter1 abst = indexing abst . representing (\f -> distribute1 . fmap f)
{-# INLINE setter1 #-}

-- | Build an 'Ixsetter1' from an indexed function.
--
-- @since 0.0.3
ixsetter1 :: ((i -> a -> b) -> a -> t) -> Ixsetter1 i a t a b
ixsetter1 f = setter1 $ \iab -> f (curry iab) . snd
{-# INLINE ixsetter1 #-}

---------------------------------------------------------------------
-- Dual Constructors
---------------------------------------------------------------------

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
cosetter abst = coindexing abst . corepresenting (\f -> fmap f . sequenceA)
{-# INLINE cosetter #-}

---------------------------------------------------------------------
-- Cosetter1
---------------------------------------------------------------------

-- | TODO: Document
--
-- @since 0.0.3
cosetter1 :: ((a -> t) -> s -> t) -> Cosetter1 s t a t
cosetter1 abst = coindexing abst . corepresenting (\f -> fmap f . sequence1)
{-# INLINE cosetter1 #-}

-- TODO: cxsetter, cxsetter1 — coindexed setter constructors need
-- more investigation into the Cxoptic threading pattern.

---------------------------------------------------------------------
-- Optics
---------------------------------------------------------------------

-- | 'Setter' on each value of a functor.
--
fmapped :: Functor f => Setter (f a) (f b) a b
fmapped = setter fmap
{-# INLINE fmapped #-}

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

-- | 'Ixsetter' on each value of a representable functor.
--
-- >>> 1 :+ 2 & ixany imappedRep %~ bool 20 10 . getAny
-- 20 :+ 10
--
imappedRep :: F.Representable f => Ixsetter (F.Rep f) (f a) (f b) a b
imappedRep = ixsetter F.imapRep
{-# INLINE imappedRep #-}

-- | Map contravariantly over the input of a profunctor.
--
-- The most common profunctor to use this with is @(->)@.
--
-- @
-- ('domain' '..~' f) g x ≡ g (f x)
-- @
--
-- >>> (domain ..~ show) length [1,2,3]
-- 7
--
domain :: Profunctor p => Setter (p b r) (p a r) a b
domain = setter lmap
{-# INLINE domain #-}

-- | Map covariantly over the output of a profunctor.
--
-- The most common profunctor to use this with is @(->)@.
--
-- @
-- (codomain ..~ f) g x ≡ f (g x)
-- codomain @(->) ≡ 'Data.Profunctor.Optic.Lens.withColens' 'Data.Profunctor.Closed.closed' 'Data.Profunctor.Optic.Setter.closing'
-- @
--
-- >>> (codomain ..~ show) length [1,2,3]
-- "3"
--
codomain :: Profunctor p => Setter (p r a) (p r b) a b
codomain = setter rmap
{-# INLINE codomain #-}

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
conditioned :: (a -> Bool) -> Setter' a a
conditioned p = setter $ \f a -> if p a then f a else a
{-# INLINE conditioned #-}

---------------------------------------------------------------------
-- Dual Optics
---------------------------------------------------------------------

-- | TODO: Document
--
coliftedA :: Applicative f => Cosetter (f a) (f b) a b
coliftedA p = cotabulate $ fmap (cosieve p) . sequenceA
{-# INLINE coliftedA #-}

-- | TODO: Document
--
-- @since 0.0.3
coliftedF :: Apply f => Cosetter1 (f a) (f b) a b
coliftedF p = cotabulate $ fmap (cosieve p) . sequence1
{-# INLINE coliftedF #-}

-- | Variant of 'coliftedA' specialized to zip-toListOf.
--
-- Useful because toListOf are not 'Control.Coapplicative.Coapplicative'.
--
-- @since 0.0.3
zipListed :: Cosetter [a] [b] a b
zipListed = dimap ZipList getZipList . coliftedA
{-# INLINE zipListed #-}

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

-- | Set the focus of a 'Setter'.
--
sets ::  ASetter s t a b -> (a -> b) -> s -> t
sets o = (runIdentity #.) #. traverseOf o .# (Identity #.)
{-# INLINE sets #-}

-- | Set the focus of a 'Ixsetter'.
--
-- @since 0.0.3
ixsets :: Monoid i => AIxsetter i s t a b -> (i -> a -> b) -> s -> t
ixsets o f = curry (sets o $ uncurry f) mempty
{-# INLINE ixsets #-}

---------------------------------------------------------------------
-- Dual Operators
---------------------------------------------------------------------

-- | Set the focus of a 'Cosetter'.
--
-- @
-- 'coset' o b = (o '/~' b) . 'Data.Functor.Identity'
-- @
--
coset :: ACosetter s t a b -> b -> s -> t
coset o b = cosets o $ const b

-- | Set the focus of a 'Cxsetter'.
--
-- Equivalent to 'cxsets' with the current value ignored.
--
-- @since 0.0.3
cxset :: Monoid i => ACxsetter i s t a b -> (i -> b) -> s -> t
cxset o ib = cxsets o $ flip (const ib)
{-# INLINE cxset #-}

-- | Set the focus of a 'Cosetter'.
--
cosets :: ACosetter s t a b -> (a -> b) -> s -> t
cosets o = (.# Identity) #. cotraverseOf o .# (.# runIdentity)
{-# INLINE cosets #-}

-- | Set the focus of a 'Cxsetter'.
--
-- @since 0.0.3
cxsets :: Monoid i => ACxsetter i s t a b -> (i -> a -> b) -> s -> t
cxsets o f = flip (cosets o $ flip f) mempty
{-# INLINE cxsets #-}

---------------------------------------------------------------------
-- MonadState / MonadReader / MonadWriter
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

-- | Indexed 'assigns': replace the target(s) of an indexed settable
-- in a monadic state.
--
-- @since 0.0.3
ixassigns :: MonadState s m => Monoid i => Ixoptic (->) i s s a b -> (i -> b) -> m ()
ixassigns o f = State.modify (ixover o (const . f))
{-# INLINE ixassigns #-}

-- | Indexed 'modifies': map over the target(s) of an indexed settable
-- in a monadic state.
--
-- @since 0.0.3
ixmodifies :: MonadState s m => Monoid i => Ixoptic (->) i s s a b -> (i -> a -> b) -> m ()
ixmodifies o f = State.modify (ixover o f)
{-# INLINE ixmodifies #-}

-- | Modify the value of a 'Reader' environment.
--
-- @
-- 'localizes' l 'id' a ≡ a
-- 'localizes' l f '.' localizes l g ≡ 'localizes' l (f '.' g)
-- @
--
-- >>> (1,1) & localizes first' (+1) (uncurry (+))
-- 3
-- >>> "," & localizes (setter ($)) ("Hello" <>) (<> " world!")
-- "Hello, world!"
--
-- Compare 'forwarded'.
--
localizes :: MonadReader s m => Optic (->) s s a b -> (a -> b) -> m r -> m r
localizes o f = Reader.local (o f)
{-# INLINE localizes #-}

-- | Write to a fragment of a larger 'Writer' format.
--
tells :: MonadWriter w m => Monoid s => Optic (->) s w a b -> b -> m ()
tells o b = Writer.tell (o (const b) mempty)
{-# INLINE tells #-}

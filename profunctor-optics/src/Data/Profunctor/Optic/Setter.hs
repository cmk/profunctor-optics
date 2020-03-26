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
  , Resetter
  , Resetter'
  , setter
  , closing
  , resetter
    -- * Setter1
  , Setter1
  , Setter1'
  , Resetter1
  , Resetter1'
  , setter1
  , resetter1
    -- * Optics
  , cod
  , dom
  , fmapped
  , omapped
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
  , (.~)
  , (..~)
  , set
  , sets
  , reset
  , resets
    -- * mtl
  , (.=)
  , (..=)
  , assigns
  , modifies
  , locally
  , scribe
) where

import Control.Applicative (liftA,ZipList(..))
import Control.Monad.Reader as Reader
import Control.Monad.State as State
import Control.Monad.Writer as Writer
import Data.MonoTraversable (Element, MonoComonad(..), MonoFunctor(..))
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Import hiding ((&&&))
import Data.Profunctor.Optic.Combinator
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Iso (sieved,cosieved)
import Data.Profunctor.Optic.Traversal

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
-- >>> import Data.Tuple (swap)
-- >>> :load Data.Profunctor.Optic

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

-- | Every valid 'Grate' is a 'Setter'.
--
closing :: (((s -> a) -> b) -> t) -> Setter s t a b
closing sabt = setter $ \ab s -> sabt $ \sa -> ab (sa s)
{-# INLINE closing #-}

-- | Obtain a 'Resetter' from a <http://conal.net/blog/posts/semantic-editor-combinators SEC>.
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input function satisfies the following
-- properties:
--
-- * @abst id ≡ id@
--
-- * @abst f . abst g ≡ abst (f . g)@
--
resetter :: ((a -> t) -> s -> t) -> Resetter s t a t
resetter abst = cosieved abst . corepresent (\f -> fmap f . sequenceA)
{-# INLINE resetter #-}

---------------------------------------------------------------------
-- Setter1
---------------------------------------------------------------------

-- | TODO: Document
--
setter1 :: ((a -> b) -> a -> t) -> Setter1 a t a b
setter1 abst = sieved abst . represent (\f -> distribute1 . fmap f)
{-# INLINE setter1 #-}

-- | TODO: Document
--
resetter1 :: ((a -> t) -> s -> t) -> Resetter1 s t a t
resetter1 abst = cosieved abst . corepresent (\f -> fmap f . sequence1)
{-# INLINE resetter1 #-}

---------------------------------------------------------------------
-- Optics 
---------------------------------------------------------------------

-- | Map covariantly over the output of a profunctor.
--
-- The most common profunctor to use this with is @(->)@.
--
-- @
-- (dom ..~ f) g x ≡ f (g x)
-- cod @(->) ≡ 'Data.Profunctor.Optic.Lens.withGrate' 'Data.Profunctor.Closed.closed' 'Data.Profunctor.Optic.Setter.closing'
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

-- | 'Setter' on each value of a monofunctor.
--
omapped :: MonoFunctor a => Setter' a (Element a)
omapped = setter omap
{-# INLINE omapped #-}

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
reliftedA :: Applicative f => Resetter (f a) (f b) a b
reliftedA p = cotabulate $ fmap (cosieve p) . sequenceA
{-# INLINE reliftedA #-}

-- | TODO: Document
--
reliftedF :: Apply f => Resetter1 (f a) (f b) a b
reliftedF p = cotabulate $ fmap (cosieve p) . sequence1
{-# INLINE reliftedF #-}

-- | Variant of 'reliftedA' specialized to zip-lists.
--
-- Useful because lists are not 'Control.Coapplicative.Coapplicative'.
--
zipListed :: Resetter [a] [b] a b
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
set :: ASetter Identity s t a b -> b -> s -> t
set o b = sets o $ const b
{-# INLINE set #-}

-- | TODO: Document
--
sets ::  ASetter Identity s t a b -> (a -> b) -> s -> t
sets o = (runIdentity #.) #. traverses o .# (Identity #.)
{-# INLINE sets #-}

-- | Set the focus of a 'Resetter'.
--
-- @
-- 'reset' o b = (o '/~' b) . 'Data.Functor.Identity'
-- @
--
reset :: AResetter Identity s t a b -> b -> s -> t
reset o b = resets o $ const b

-- | TODO: Document
--
resets :: AResetter Identity s t a b -> (a -> b) -> s -> t
resets o = (.# Identity) #. cotraverses o .# (.# runIdentity) 
{-# INLINE resets #-}


---------------------------------------------------------------------
-- Mtl
---------------------------------------------------------------------

infix 4 .=, ..=

-- | Replace the target(s) of a settable in a monadic state.
--
-- This is an infixversion of 'assigns'.
--
-- >>> execState (do first' .= 1; second' .= 2) (3,4)
-- (1,2)
-- >>> execState (both .= 3) (1,2)
-- (3,3)
--
(.=) :: MonadState s m => Optic (->) s s a b -> b -> m ()
o .= b = State.modify (o .~ b)
{-# INLINE (.=) #-}

-- | Map over the target(s) of a 'Setter' in a monadic state.
--
-- This is an infixversion of 'modifies'.
--
-- >>> execState (do just ..= (+1) ) Nothing
-- Nothing
-- >>> execState (do first' ..= (+1) ;second' ..= (+2)) (1,2)
-- (2,4)
-- >>> execState (do both ..= (+1)) (1,2)
-- (2,3)
--
(..=) :: MonadState s m => Optic (->) s s a b -> (a -> b) -> m ()
o ..= f = State.modify (o ..~ f)
{-# INLINE (..=) #-}

-- | A prefix alias for '.='.
--
assigns :: MonadState s m => Optic (->) s s a b -> b -> m ()
assigns = (.=)
{-# INLINE assigns #-}

-- | A prefix alias for '..='
--
modifies :: MonadState s m => Optic (->) s s a b -> (a -> b) -> m ()
modifies = (..=)
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
locally o f = Reader.local $ o ..~ f
{-# INLINE locally #-}

-- | Write to a fragment of a larger 'Writer' format.
--
scribe :: MonadWriter w m => Monoid s => Optic (->) s w a b -> b -> m ()
scribe o b = Writer.tell (mempty & o .~ b)
{-# INLINE scribe #-}

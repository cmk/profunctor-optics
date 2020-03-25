{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Setter where
{-(
    -- * Adjoint
    Adjoint
  , Adjoint'
  , adjointl
  , adjointr
  , alower
  , aupper
    -- * Optics
  , sec
  , cod
  , dom
  , fmapped
  , contramapped
  , liftedM
  , liftedA
  , forwarded
  , censored
  , mappedException
    -- * Operators
  , set
  , over
  , (.~)
  , (..~)
  , lifts
  , lowers
    -- * mtl
  , (.=)
  , (..=)
  , assigns
  , modifies
  , locally
  , scribe
) where
-}

import Control.Exception (Exception)
import Control.Applicative (liftA,ZipList(..))
import Control.Monad.Reader as Reader
import Control.Monad.State as State
import Control.Monad.Writer as Writer
import Data.Profunctor.Optic.Import hiding ((&&&))
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Iso
import Data.Profunctor.Optic.Traversal
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Combinator
import qualified Control.Exception as Ex

import Data.Profunctor.Optic.Lens
import qualified Data.Functor.Rep as F
import Data.Profunctor.Closed
import Data.Profunctor.Rep
import qualified Data.Bifunctor as B

import qualified Data.Functor.Rep as F



--voided' a = corepresent $ \f -> f unabsurdL a
--zapWithAdjunction :: Adjunction f u => (a -> b -> c) -> u a -> f b -> c 
--tabulateAdjunction :: Adjunction f u => (f () -> b) -> u b 
--indexAdjunction :: Adjunction f u => u b -> f a -> b 
--cozipL :: Adjunction f u => f (Either a b) -> Either (f a) (f b) 


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
-- Adjoint
---------------------------------------------------------------------

adjointl :: (forall l u. Adjunction l u => (a -> u b) -> l s -> t) -> Adjoint s t a b
adjointl f = corepresent $ f . leftAdjunct

adjointr :: (forall l u. Adjunction l u => (l a -> b) -> s -> u t) -> Adjoint s t a b
adjointr f = represent $ f . rightAdjunct

-- > alower = acostar . over adjuncted . stars . aupper
alower :: Adjunction l u => ((a -> b) -> s -> t) -> CostarLike l s t a b
alower = acostar . over adjuncted . stars . aupper

-- > aupper = astar . over (invert adjuncted) . costars . alower
aupper :: F.Representable u => ((a -> b) -> s -> t) -> StarLike u s t a b
aupper f = astar $ \afb s -> F.tabulate $ \i -> f (flip F.index i . afb) s

---------------------------------------------------------------------
-- Optics 
---------------------------------------------------------------------

-- | The identity for 'Adjoint' optics.
--
-- > adjoined = adjointl rightAdjunct = adjointr leftAdjunct
--
adjoined :: Adjoint a b a b
adjoined = adjointl rightAdjunct 

zapped :: (s -> a) -> (s -> b -> t) -> Adjoint s t a b
zapped sa sbt = adjointl $ \ab s -> zapWithAdjunction (flip sbt) (ab . sa $ extractL s) s

cozapped :: (s -> t + a) -> (b -> t) -> Adjoint s t a b
cozapped sta bt = adjointl $ \ab s -> either extractL (bt . rightAdjunct ab) . cozipL $ fmap sta s



-- | Obtain a 'Adjoint' from a <http://conal.net/blog/posts/semantic-editor-combinators SEC>.
--
-- To demote an optic to a semantic editor combinator, use the section @(l ..~)@ or @over l@.
--
-- >>> [("The",0),("quick",1),("brown",1),("fox",2)] & sec fmap . first' ..~ Prelude.length
-- [(3,0),(5,1),(5,1),(3,2)]
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input function satisfies the following
-- properties:
--
-- * @abst id = id@
--
-- * @abst f . abst g = abst (f . g)@
--
-- More generally, a profunctor optic must be monoidal as a natural 
-- transformation:
-- 
-- * @o id = id@
--
-- * @o ('Data.Profunctor.Composition.Procompose' p q) = 'Data.Profunctor.Composition.Procompose' (o p) (o q)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
sec :: ((a -> b) -> s -> t) -> Adjoint s t a b
sec abst = iso (flip Index id) (\(Index s ab) -> abst ab s) . represent collect
{-# INLINE sec #-}

-- | Map covariantly over the output of a profunctor.
--
-- The most common profunctor to use this with is @(->)@.
--
-- @
-- (dom ..~ f) g x = f (g x)
-- cod @(->) = 'Data.Profunctor.Optic.Lens.withGrate' 'Data.Profunctor.Closed.closed' 'Data.Profunctor.Optic.Adjoint.closing'
-- @
--
-- >>> (cod ..~ show) length [1,2,3]
-- "3"
--
cod :: Profunctor p => Adjoint (p r a) (p r b) a b
cod = sec rmap
{-# INLINE cod #-}

-- | Map contravariantly over the input of a profunctor.
--
-- The most common profunctor to use this with is @(->)@.
--
-- @
-- ('dom' '..~' f) g x = g (f x)
-- @
--
-- >>> (dom ..~ show) length [1,2,3]
-- 7
--
dom :: Profunctor p => Adjoint (p b r) (p a r) a b
dom = sec lmap
{-# INLINE dom #-}

-- | 'Adjoint' on each value of a functor.
--
-- @
-- 'fmapped' = 'sec' 'fmap' = 'tabulate' . 'collect' . 'sieve'
-- @
--
fmapped :: Functor f => Adjoint (f a) (f b) a b
fmapped = sec fmap
{-# INLINE fmapped #-}

-- | 'Adjoint' on each value of a contravariant functor.
--
-- @
-- 'Data.Functor.Contravariant.contramap' = 'over' 'contramapped'
-- @
--
-- >>> getPredicate (over contramapped (*2) (Predicate even)) 5
-- True
-- >>> getOp (over contramapped (*5) (Op show)) 100
-- "500"
--
contramapped :: Contravariant f => Adjoint (f b) (f a) a b
contramapped = sec contramap
{-# INLINE contramapped #-}

-- | 'Adjoint' on each value of a monad.
--
liftedM :: Monad m => Adjoint (m a) (m b) a b
liftedM = sec liftM
{-# INLINE liftedM #-}

-- | 'Adjoint' on each value of an applicative.
--
-- @
-- 'Control.Applicative.liftA' = 'sec' 'liftedA'
-- @
--
-- >>> sec liftedA Identity [1,2,3]
-- [Identity 1,Identity 2,Identity 3]
-- >>> set liftedA 2 (Just 1)
-- Just 2
--
liftedA :: Applicative f => Adjoint (f a) (f b) a b
liftedA = sec liftA
{-# INLINE liftedA #-}

-- | 'Adjoint' on the local environment of a 'Reader'. 
--
-- Use to lift reader actions into a larger environment:
--
-- >>> runReader (ask & forwarded ..~ fst) (1,2)
-- 1
--
forwarded :: Adjoint (ReaderT r2 m a) (ReaderT r1 m a) r1 r2
forwarded = sec withReaderT
{-# INLINE forwarded #-}

-- | TODO: Document
--
censored :: Writer.MonadWriter w m => Adjoint' (m a) w
censored = sec Writer.censor
{-# INLINE censored #-}

-- | Map one exception into another as proposed in the paper "A semantics for imprecise exceptions".
--
-- >>> handles (only Overflow) (\_ -> return "caught") $ assert False (return "uncaught") & (mappedException ..~ \ (AssertionFailed _) -> Overflow)
-- "caught"
--
-- @
-- emapped :: Exception e => Adjoint s s SomeException e
-- @
--
mappedException :: Exception e1 => Exception e2 => Adjoint s s e1 e2
mappedException = sec Ex.mapException
{-# INLINE mappedException #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

lifts :: Adjunction l u => CostarLike l s t a b -> (l a -> b) -> s -> u t
lifts o f = leftAdjunct $ costars o f

lowers :: Adjunction l u => StarLike u s t a b -> (a -> u b) -> l s -> t
lowers o f = rightAdjunct $ stars o f

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

-- | Map over the target(s) of a 'Adjoint' in a monadic state.
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
-- 'locally' l 'id' a = a
-- 'locally' l f '.' locally l g = 'locally' l (f '.' g)
-- @
--
-- >>> (1,1) & locally first' (+1) (uncurry (+))
-- 3
-- >>> "," & locally (sec ($)) ("Hello" <>) (<> " world!")
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

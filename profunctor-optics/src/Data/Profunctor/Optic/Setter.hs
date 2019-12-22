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
  , setter
  , isetter
  , closing
    -- * Resetter
  , Resetter
  , Resetter'
  , resetter
  , ksetter
    -- * Optics
  , cod
  , dom
  , bound 
  , fmapped
  , imappedRep
  , contramapped
  , exmapped
  , liftedA
  , liftedM
  , forwarded
  , censored
  , seeked
  , zipped
  , modded
  , cond
    -- * Primitive operators
  , withIxsetter
  , withCxsetter
    -- * Operators
  , set
  , iset
  , kset
  , (.~)
  , (%~)
  , (#~)
  , over
  , iover
  , kover
  , (..~)
  , (%%~)
  , (##~)
  , (<>~)
  , (><~)
    -- * mtl
  , locally
  , scribe
  , assigns
  , modifies
  , (.=)
  , (%=)
  , (#=)
  , (..=)
  , (%%=)
  , (##=)
  , (<>=)
  , (><=)
) where

import Control.Applicative (liftA)
import Control.Comonad.Store.Class (ComonadStore, seeks)
import Control.Exception (Exception(..))
import Control.Monad.Reader as Reader
import Control.Monad.State as State
import Control.Monad.Writer as Writer
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Import hiding ((&&&))
import Data.Profunctor.Optic.Index
import Data.Profunctor.Optic.Operator
import Data.Profunctor.Optic.Types
import Data.Semiring

import qualified Control.Exception as Ex
import qualified Data.Functor.Rep as F

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> :set -XRankNTypes
-- >>> import Control.Category ((>>>))
-- >>> import Control.Arrow (Kleisli(..))
-- >>> import Control.Exception
-- >>> import Control.Monad.State
-- >>> import Control.Monad.Reader
-- >>> import Control.Monad.Writer
-- >>> import Data.Bool (bool)
-- >>> import Data.Bool.Instance ()
-- >>> import Data.Complex
-- >>> import Data.Functor.Rep
-- >>> import Data.Functor.Identity
-- >>> import Data.Functor.Contravariant
-- >>> import Data.Int.Instance ()
-- >>> import Data.List.Index as LI
-- >>> import Data.IntSet as IntSet
-- >>> import Data.Set as Set
-- >>> import Data.Tuple (swap)
-- >>> :load Data.Profunctor.Optic Data.Either.Optic Data.Tuple.Optic
-- >>> let catchOn :: Int -> Cxprism' Int (Maybe String) String ; catchOn n = kjust $ \k -> if k==n then Just "caught" else Nothing
-- >>> let itraversed :: Ixtraversal Int [a] [b] a b ; itraversed = itraversalVl itraverse
-- >>> let iat :: Int -> Ixaffine' Int [a] a; iat i = iaffine' (\s -> flip LI.ifind s $ \n _ -> n==i) (\s a -> LI.modifyAt i (const a) s) 

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
setter abst = dimap (flip Index id) (\(Index s ab) -> abst ab s) . repn collect
{-# INLINE setter #-}

-- | Build an 'Ixsetter' from an indexed function.
--
-- @
-- 'isetter' '.' 'iover' ≡ 'id'
-- 'iover' '.' 'isetter' ≡ 'id'
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
isetter :: ((i -> a -> b) -> s -> t) -> Ixsetter i s t a b
isetter f = setter $ \iab -> f (curry iab) . snd 
{-# INLINE isetter #-}

-- | Every valid 'Grate' is a 'Setter'.
--
closing :: (((s -> a) -> b) -> t) -> Setter s t a b
closing sabt = setter $ \ab s -> sabt $ \sa -> ab (sa s)
{-# INLINE closing #-}

---------------------------------------------------------------------
-- Resetter
---------------------------------------------------------------------

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
resetter abst = dimap (\s -> Coindex $ \ab -> abst ab s) trivial . corepn (\f -> fmap f . sequenceA)
{-# INLINE resetter #-}

-- | TODO: Document
--
-- /Caution/: In order for the generated optic to be well-defined,
-- you must ensure that the input satisfies the following properties:
--
-- * @kabst (const id) ≡ id@
--
-- * @fmap (kabst $ const f) . (kabst $ const g) ≡ kabst (const $ f . g)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
ksetter :: ((k -> a -> t) -> s -> t) -> Cxsetter k s t a t
ksetter f = resetter $ \kab -> const . f (flip kab)
{-# INLINE ksetter #-}

---------------------------------------------------------------------
-- Optics 
---------------------------------------------------------------------

-- | Map covariantly over the output of a 'Profunctor'.
--
-- The most common profunctor to use this with is @(->)@.
--
-- @
-- (dom ..~ f) g x ≡ f (g x)
-- cod @(->) ≡ 'Data.Profunctor.Optic.Grate.withGrate' 'Data.Profunctor.Closed.closed' 'Data.Profunctor.Optic.Setter.closing'
-- @
--
-- >>> (cod ..~ show) length [1,2,3]
-- "3"
--
cod :: Profunctor p => Setter (p r a) (p r b) a b
cod = setter rmap
{-# INLINE cod #-}

-- | Map contravariantly over the input of a 'Profunctor'.
--
-- The most common profunctor to use this with is @(->)@.
--
-- @
-- (dom ..~ f) g x ≡ g (f x)
-- @
--
-- >>> (dom ..~ show) length [1,2,3]
-- 7
--
dom :: Profunctor p => Setter (p b r) (p a r) a b
dom = setter lmap
{-# INLINE dom #-}

-- | 'Setter' for monadically transforming a monadic value.
--
bound :: Monad m => Setter (m a) (m b) a (m b)
bound = setter (=<<)
{-# INLINE bound #-}

-- | 'Setter' on each value of a functor.
--
fmapped :: Functor f => Setter (f a) (f b) a b
fmapped = setter fmap
{-# INLINE fmapped #-}

-- | 'Ixsetter' on each value of a representable functor.
--
-- >>> 1 :+ 2 & imappedRep %~ bool 20 10
-- 20 :+ 10
--
imappedRep :: F.Representable f => Ixsetter (F.Rep f) (f a) (f b) a b
imappedRep = isetter F.imapRep
{-# INLINE imappedRep #-}

-- | 'Setter' on each value of a contravariant functor.
--
-- @
-- 'contramap' ≡ 'over' 'contramapped'
-- @
--
-- >>> getPredicate (over contramapped (*2) (Predicate even)) 5
-- True
--
-- >>> getOp (over contramapped (*5) (Op show)) 100
-- "500"
--
contramapped :: Contravariant f => Setter (f b) (f a) a b
contramapped = setter contramap
{-# INLINE contramapped #-}

-- | Map one exception into another as proposed in the paper "A semantics for imprecise exceptions".
--
-- >>> handles (only Overflow) (\_ -> return "caught") $ assert False (return "uncaught") & (exmapped ..~ \ (AssertionFailed _) -> Overflow)
-- "caught"
--
-- @
-- exmapped :: Exception e => Setter s s SomeException e
-- @
--
exmapped :: Exception e1 => Exception e2 => Setter s s e1 e2
exmapped = setter Ex.mapException
{-# INLINE exmapped #-}

-- | 'Setter' on each value of an applicative.
--
-- @
-- 'liftA' ≡ 'setter' 'liftedA'
-- @
--
-- >>> setter liftedA Identity [1,2,3]
-- [Identity 1,Identity 2,Identity 3]
--
-- >>> set liftedA 2 (Just 1)
-- Just 2
--
liftedA :: Applicative f => Setter (f a) (f b) a b
liftedA = setter liftA
{-# INLINE liftedA #-}

-- | 'Setter' on each value of a monad.
--
liftedM :: Monad m => Setter (m a) (m b) a b
liftedM = setter liftM
{-# INLINE liftedM #-}

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

-- | 'Setter' on the 
--
seeked :: ComonadStore a w => Setter' (w s) a
seeked = setter seeks
{-# INLINE seeked #-}

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
-- See also 'Data.Profunctor.Optic.Affine.predicated' & 'Data.Profunctor.Optic.Prism.filtered'.
--
cond :: (a -> Bool) -> Setter' a a
cond p = setter $ \f a -> if p a then f a else a
{-# INLINE cond #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

infixr 4 <>~, ><~

-- | Prefix variant of '.~'.
--
-- @ 'set' l y ('set' l x a) ≡ 'set' l y a @
--
set :: Optic (->) s t a b -> b -> s -> t
set = (.~)
{-# INLINE set #-}

-- | Prefix alias of '%~'.
--
-- Equivalent to 'iover' with the current value ignored.
--
-- @
-- 'set' o ≡ 'iset' o '.' 'const'
-- @
--
-- >>> iset (iat 2) (2-) [1,2,3 :: Int]
-- [1,2,0]
--
-- >>> iset (iat 5) (const 0) [1,2,3 :: Int]
-- [1,2,3]
--
iset :: Monoid i => AIxsetter i s t a b -> (i -> b) -> s -> t
iset o = iover o . (const .)
{-# INLINE iset #-}

-- | Prefix alias of '#~'.
--
-- Equivalent to 'kover' with the current value ignored.
--
kset :: Monoid k => ACxsetter k s t a b -> (k -> b) -> s -> t 
kset o kb = kover o $ flip (const kb)
{-# INLINE kset #-}

-- | Prefix alias of '..~'.
--
-- @
-- 'over' o 'id' ≡ 'id' 
-- 'over' o f '.' 'over' o g ≡ 'over' o (f '.' g)
-- 'over' '.' 'setter' ≡ 'id'
-- 'over' '.' 'resetter' ≡ 'id'
-- @
--
-- >>> over fmapped (+1) (Just 1)
-- Just 2
--
-- >>> over fmapped (*10) [1,2,3]
-- [10,20,30]
--
-- >>> over first' (+1) (1,2)
-- (2,2)
--
-- >>> over first' show (10,20)
-- ("10",20)
--
over :: Optic (->) s t a b -> (a -> b) -> s -> t
over = id
{-# INLINE over #-}

-- | Prefix alias of '%%~'.
--
-- >>> iover (iat 1) (+) [1,2,3 :: Int]
-- [1,3,3]
--
-- >>> iover (iat 5) (+) [1,2,3 :: Int]
-- [1,2,3]
--
iover :: Monoid i => AIxsetter i s t a b -> (i -> a -> b) -> s -> t
iover = (%%~)
{-# INLINE iover #-}

-- | Prefix alias of '##~'.
--
kover :: Monoid k => ACxsetter k s t a b -> (k -> a -> b) -> s -> t 
kover = (##~)
{-# INLINE kover #-}

-- | Modify the target by adding another value.
--
-- >>> both <>~ True $ (False,True)
-- (True,True)
--
-- >>> both <>~ "!" $ ("bar","baz")
-- ("bar!","baz!")
--
(<>~) :: Semigroup a => Optic (->) s t a a -> a -> s -> t
l <>~ n = over l (<> n)
{-# INLINE (<>~) #-}

-- | Modify the target by multiplying by another value.
--
-- >>> both ><~ False $ (False,True)
-- (False,False)
--
-- >>> both ><~ ["!"] $ (["bar","baz"], [])
-- (["bar!","baz!"],[])
--
(><~) :: Semiring a => Optic (->) s t a a -> a -> s -> t
l ><~ n = over l (>< n)
{-# INLINE (><~) #-}

---------------------------------------------------------------------
-- Mtl
---------------------------------------------------------------------

-- | Modify the value of a 'Reader' environment.
--
-- @
-- 'locally' l 'id' a ≡ a
-- 'locally' l f '.' locally l g ≡ 'locally' l (f '.' g)
-- @
--
-- >>> (1,1) & locally first' (+1) (uncurry (+))
-- 3
--
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
scribe :: MonadWriter w m => Monoid b => Optic (->) s w a b -> s -> m ()
scribe o s = Writer.tell $ set o mempty s
{-# INLINE scribe #-}

infix 4 .=, ..=, %=, %%=, #=, ##=, <>=, ><=

-- | Replace the target(s) of a settable in a monadic state.
--
assigns :: MonadState s m => Optic (->) s s a b -> b -> m ()
assigns o b = State.modify (set o b)
{-# INLINE assigns #-}

-- | Map over the target(s) of a 'Setter' in a monadic state.
--
modifies :: MonadState s m => Optic (->) s s a b -> (a -> b) -> m ()
modifies o f = State.modify (over o f)
{-# INLINE modifies #-}

-- | Replace the target(s) of a settable in a monadic state.
--
-- This is an infixversion of 'assigns'.
--
-- >>> execState (do first' .= 1; second' .= 2) (3,4)
-- (1,2)
--
-- >>> execState (both .= 3) (1,2)
-- (3,3)
--
(.=) :: MonadState s m => Optic (->) s s a b -> b -> m ()
o .= b = State.modify (o .~ b)
{-# INLINE (.=) #-}

-- | TODO: Document 
--
(%=) :: MonadState s m => Monoid i => AIxsetter i s s a b -> (i -> b) -> m ()
o %= b = State.modify (o %~ b)
{-# INLINE (%=) #-}

-- | TODO: Document 
--
(#=) :: MonadState s m => Monoid k => ACxsetter k s s a b -> (k -> b) -> m ()
o #= f = State.modify (o #~ f)
{-# INLINE (#=) #-}

-- | Map over the target(s) of a 'Setter' in a monadic state.
--
-- This is an infixversion of 'modifies'.
--
-- >>> execState (do just ..= (+1) ) Nothing
-- Nothing
--
-- >>> execState (do first' ..= (+1) ;second' ..= (+2)) (1,2)
-- (2,4)
--
-- >>> execState (do both ..= (+1)) (1,2)
-- (2,3)
--
(..=) :: MonadState s m => Optic (->) s s a b -> (a -> b) -> m ()
o ..= f = State.modify (o ..~ f)
{-# INLINE (..=) #-}

-- | TODO: Document 
--
(%%=) :: MonadState s m => Monoid i => AIxsetter i s s a b -> (i -> a -> b) -> m () 
o %%= f = State.modify (o %%~ f)
{-# INLINE (%%=) #-}

-- | TODO: Document 
--
(##=) :: MonadState s m => Monoid k => ACxsetter k s s a b -> (k -> a -> b) -> m () 
o ##= f = State.modify (o ##~ f)
{-# INLINE (##=) #-}

-- | Modify the target(s) of a settable optic by adding a value.
--
-- >>> execState (both <>= False) (False,True)
-- (False,True)
--
-- >>> execState (both <>= "!!!") ("hello","world")
-- ("hello!!!","world!!!")
--
(<>=) :: MonadState s m => Semigroup a => Optic' (->) s a -> a -> m ()
o <>= a = State.modify (o <>~ a)
{-# INLINE (<>=) #-}

-- | Modify the target(s) of a settable optic by mulitiplying by a value.
--
-- >>> execState (both ><= False) (False,True)
-- (False,False)
--
(><=) :: MonadState s m => Semiring a => Optic' (->) s a -> a -> m ()
o ><= a = State.modify (o ><~ a)
{-# INLINE (><=) #-}

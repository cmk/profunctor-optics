{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Setter (
    -- * Types
    Setter
  , Setter'
  , ASetter
  , ASetter'
  , Resetter
  , Resetter'
  , AResetter
  , AResetter'
    -- * Constructors
  , setter
  , resetter
  , closing
  , (<%>)
  , toSemiring
  , fromSemiring
    -- * Primitive operators
  , over
  , under
    -- * Common optics
  , zero
  , one
  , cod
  , dom
  , bound 
  , fmapped
  , contramapped
  , foldMapped
  , liftedA
  , liftedM
  , sets
  , zipped
  , modded
  , branched
  , reviewed
  , composed
  , exmapped
    -- * Derived operators
  , (%~)
  , (.~)
  , set
  , reset
  , assignsA
  , (?~)
  , (<>~)
  , (><~)
    -- * MonadState
  , (.=)
  , assigns
  , (%=)
  , modifies
  , (?=)
  , (<>=)
  , (><=)
) where

import Control.Applicative (liftA)
import Control.Exception (Exception(..))
import Control.Monad.State as State hiding (lift)
import Control.Monad.Writer as Writer hiding (lift)
import Data.Foldable (Foldable, foldMap)
import Data.Profunctor.Arrow
import Data.Profunctor.Optic.Iso (Context(..), Indexed(..), trivial)
import Data.Profunctor.Optic.Import hiding ((&&&))
import Data.Profunctor.Optic.Type
import Data.Semiring
import qualified Control.Exception as Ex

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> import Control.Category ((>>>))
-- >>> import Control.Arrow (Kleisli(..))
-- >>> import Control.Exception
-- >>> import Control.Monad.State
-- >>> import Control.Monad.Writer
-- >>> import Data.Functor.Identity
-- >>> import Data.Functor.Contravariant
-- >>> :load Data.Profunctor.Optic

---------------------------------------------------------------------
-- Setter
---------------------------------------------------------------------

-- | Obtain a 'Setter' from a <http://conal.net/blog/posts/semantic-editor-combinators SEC>.
--
-- To demote an optic to a semantic edit combinator, use the section @(l %~)@ or @over l@.
--
-- >>> [("The",0),("quick",1),("brown",1),("fox",2)] & setter map . first %~ length
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
setter abst = dimap (flip Context id) (\(Context s ab) -> abst ab s) . lift collect

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
-- More generally, a profunctor optic must be monoidal as a natural 
-- transformation:
-- 
-- * @o id ≡ id@
--
-- * @o ('Data.Profunctor.Composition.Procompose' p q) ≡ 'Data.Profunctor.Composition.Procompose' (o p) (o q)@
--
-- See 'Data.Profunctor.Optic.Property'.
--
resetter :: ((a -> t) -> s -> t) -> Resetter s t a t
resetter abst = dimap (\s -> Indexed $ \ab -> abst ab s) trivial . colift (\f -> fmap f . sequence1)

-- | Every valid 'Grate' is a 'Setter'.
--
closing :: (((s -> a) -> b) -> t) -> Setter s t a b
closing sabt = setter $ \ab s -> sabt $ \sa -> ab (sa s)

infixl 6 <%>

-- | Sum two 'Setter's
--
(<%>) :: Setter' a a -> Setter' a a -> Setter' a a
(<%>) f g = setter $ \h -> (f %~ h) . (g %~ h)

-- | Lower a semiring value to its concrete analog.
--
-- @ 
-- 'toSemiring' . 'fromSemiring' ≡ 'id'
-- 'fromSemiring' . 'toSemiring' ≡ 'id'
-- @
--
toSemiring :: Monoid a => Semiring a => Setter' a a -> a
toSemiring a = over a (unit <>) mempty

-- | Lift a semiring value to its double Cayley analog.
--
-- @ 
-- 'toSemiring' . 'fromSemiring' ≡ 'id'
-- 'fromSemiring' . 'toSemiring' ≡ 'id'
-- @
--
fromSemiring :: Monoid a => Semiring a => a -> Setter' a a
fromSemiring a = setter $ \f y -> a >< f mempty <> y

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | Extract a SEC from a 'Setter'.
--
-- Used to modify the target of a 'Lens' or all the targets of a 'Setter' 
-- or 'Traversal'.
--
-- @
-- 'over' o 'id' ≡ 'id' 
-- 'over' o f '.' 'over' o g ≡ 'over' o (f '.' g)
-- 'setter' '.' 'over' ≡ 'id'
-- 'over' '.' 'setter' ≡ 'id'
-- @
--
-- >>> over fmapped (+1) (Just 1)
-- Just 2
--
-- >>> over fmapped (*10) [1,2,3]
-- [10,20,30]
--
-- >>> over first (+1) (1,2)
-- (2,2)
--
-- >>> over first show (10,20)
-- ("10",20)
--
-- @
-- over :: Setter s t a b -> (a -> r) -> s -> r
-- over :: Monoid r => Fold s t a b -> (a -> r) -> s -> r
-- @
--
over :: ASetter s t a b -> (a -> b) -> s -> t
over o = (runIdentity #.) #. runStar #. o .# Star .# (Identity #. ) 

-- | Extract a SEC from a 'Resetter'.
--
-- @
-- 'under' o 'id' ≡ 'id' 
-- 'under' o f '.' 'under' o g ≡ 'under' o (f '.' g)
-- 'resetter' '.' 'under' ≡ 'id'
-- 'under' '.' 'resetter' ≡ 'id'
-- @
--
under :: AResetter s t a b -> (a -> b) -> s -> t
under o = (.# Identity) #. runCostar #. o .# Costar .# (.# runIdentity)

---------------------------------------------------------------------
-- Common 'Setter's & 'Resetter's
---------------------------------------------------------------------

-- | The zero 'Setter'.
--
-- @
-- 'zero'  .  'one' ≡ 'zero'
-- 'zero' <%> 'one' ≡ 'one'
-- @
--
-- >>> toSemiring $ zero <%> one :: Int
-- 1
-- >>> toSemiring $ zero  .  one :: Int
-- 0
--
zero :: Setter' a a
zero = setter $ const id
{-# INLINE zero #-}

-- | The unit 'Setter'.
--
-- @
-- 'zero'  .  'one' ≡ 'zero'
-- 'zero' <%> 'one' ≡ 'one'
-- @
--
-- >>> toSemiring $ zero <%> one :: Int
-- 1
-- >>> toSemiring $ zero  .  one :: Int
-- 0
--
one :: Setter' a a 
one = setter id
{-# INLINE one #-}

-- | Map covariantly over the output of a 'Profunctor'.
--
-- The most common profunctor to use this with is @(->)@.
--
-- @
-- (dom %~ f) g x ≡ f (g x)
-- cod @(->) ≡ 'Data.Profunctor.Optic.Grate.withGrate' 'Data.Profunctor.Closed.closed' 'Data.Profunctor.Optic.Setter.closing'
-- @
--
-- >>> (cod %~ show) length [1,2,3]
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
-- (dom %~ f) g x ≡ g (f x)
-- @
--
-- >>> (dom %~ show) length [1,2,3]
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

-- | This 'Setter' can be used to map over all of the inputs to a 'Contravariant'.
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

-- | TODO: Document
--
foldMapped :: Foldable f => Monoid m => Setter (f a) m a m
foldMapped = setter foldMap
{-# INLINE foldMapped #-}

-- | This 'setter' can be used to modify all of the values in an 'Applicative'.
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

-- | TODO: Document
--
liftedM :: Monad m => Setter (m a) (m b) a b
liftedM = setter liftM
{-# INLINE liftedM #-}

-- | Set a value using a 'Setter'.
--
sets :: Setter b (a -> c) a c
sets = setter const
{-# INLINE sets #-}

-- | TODO: Document
--
zipped :: Setter (u -> v -> a) (u -> v -> b) a b
zipped = setter ((.)(.)(.))
{-# INLINE zipped #-}

-- | TODO: Document
--
modded :: (a -> Bool) -> Setter' (a -> b) b
modded p = setter $ \mods f a -> if p a then mods (f a) else f a
{-# INLINE modded #-}

-- | Apply a function only when the given predicate holds.
--
-- See also 'Data.Profunctor.Optic.Affine.predicated' & 'Data.Profunctor.Optic.Prism.filtered'.
--
branched :: (a -> Bool) -> Setter' a a
branched p = setter $ \f a -> if p a then f a else a
{-# INLINE branched #-}

-- | TODO: Document
--
reviewed :: Setter (b -> t) (((s -> a) -> b) -> t) s a
reviewed = setter $ \sa bt sab -> bt (sab sa)
{-# INLINE reviewed #-}

-- | TODO: Document
--
composed :: Setter (s -> a) ((a -> b) -> s -> t) b t
composed = setter between
{-# INLINE composed #-}

-- | Map one exception into another as proposed in the paper "A semantics for imprecise exceptions".
--
-- >>> handles (only Overflow) (\_ -> return "caught") $ assert False (return "uncaught") & (exmapped %~ \ (AssertionFailed _) -> Overflow)
-- "caught"
--
-- @
-- exmapped :: Exception e => Setter s s SomeException e
-- @
--
exmapped :: Exception e1 => Exception e2 => Setter s s e1 e2
exmapped = setter Ex.mapException
{-# INLINE exmapped #-}

---------------------------------------------------------------------
-- Derived operators
---------------------------------------------------------------------

infixr 4 %~

-- | TODO: Document
--
(%~) :: ASetter s t a b -> (a -> b) -> s -> t
(%~) = over
{-# INLINE (%~) #-}

infixr 4 .~

-- | TODO: Document
--
(.~) :: ASetter s t a b -> b -> s -> t
(.~) = set
{-# INLINE (.~) #-}

-- | Set all referenced fields to the given value.
--
-- @ 'set' l y ('set' l x a) ≡ 'set' l y a @
--
set :: ASetter s t a b -> b -> s -> t
set o b = over o (const b)
{-# INLINE set #-}

-- | Set all referenced fields to the given value.
--
-- @
-- reset :: Resetter s t a b -> b -> s -> t
-- @
-- 
reset :: AResetter s t a b -> b -> s -> t
reset o b = under o (const b)
{-# INLINE reset #-}

-- | Run a profunctor arrow command and set the optic targets to the result.
--
-- Similar to 'assigns', except that the type of the object being modified can change.
--
-- >>> getVal1 = Right 3
-- >>> getVal2 = Right False
-- >>> action = assignsA first (Kleisli (const getVal1)) >>> assignsA second (Kleisli (const getVal2))
-- >>> runKleisli action ((), ())
-- Right (3,False)
--
-- @
-- 'assignsA' :: 'Category' p => 'Iso' s t a b       -> 'LensLike' p s t s b
-- 'assignsA' :: 'Category' p => 'Lens' s t a b      -> 'LensLike' p s t s b
-- 'assignsA' :: 'Category' p => 'Grate' s t a b     -> 'LensLike' p s t s b
-- 'assignsA' :: 'Category' p => 'Setter' s t a b    -> 'LensLike' p s t s b
-- 'assignsA' :: 'Category' p => 'Traversal' s t a b -> 'LensLike' p s t s b
-- @
--
assignsA :: Category p => ASetter s t a b -> LensLike p s t s b 
assignsA o p = arr (flip $ set o) &&& p >>> arr (uncurry id)
{-# INLINE assignsA #-}

infixr 4 ?~

-- | Set the target of a settable optic to 'Just' a value.
--
-- @
-- l '?~' t ≡ 'set' l ('Just' t)
-- @
--
-- >>> Nothing & id ?~ 1
-- Just 1
--
-- '?~' can be used type-changily:
--
-- >>> ('a', ('b', 'c')) & second . both ?~ 'x'
-- ('a',(Just 'x',Just 'x'))
--
-- @
-- ('?~') :: 'Iso' s t a ('Maybe' b)       -> b -> s -> t
-- ('?~') :: 'Lens' s t a ('Maybe' b)      -> b -> s -> t
-- ('?~') :: 'Grate' s t a ('Maybe' b)     -> b -> s -> t
-- ('?~') :: 'Setter' s t a ('Maybe' b)    -> b -> s -> t
-- ('?~') :: 'Traversal' s t a ('Maybe' b) -> b -> s -> t
-- @
--
(?~) :: ASetter s t a (Maybe b) -> b -> s -> t
o ?~ b = set o (Just b)
{-# INLINE (?~) #-}

infixl 6 <>~

-- | Modify the target by adding another value.
--
-- >>> both <>~ False $ (False,True)
-- (False,True)
--
-- >>> both <>~ "!!!" $ ("hello","world")
-- ("hello!!!","world!!!")
--
-- @
-- ('<>~') :: 'Semigroup' a => 'Iso' s t a a       -> a -> s -> t
-- ('<>~') :: 'Semigroup' a => 'Lens' s t a a      -> a -> s -> t
-- ('<>~') :: 'Semigroup' a => 'Grate' s t a a     -> a -> s -> t
-- ('<>~') :: 'Semigroup' a => 'Setter' s t a a    -> a -> s -> t
-- ('<>~') :: 'Semigroup' a => 'Traversal' s t a a -> a -> s -> t
-- @
--
(<>~) :: Semigroup a => ASetter s t a a -> a -> s -> t
l <>~ n = over l (<> n)
{-# INLINE (<>~) #-}

infixl 7 ><~

-- | Modify the target by multiplying by another value.
--
-- >>> both ><~ False $ (False,True)
-- (False,False)
--
-- @
-- ('><~') :: 'Semiring' a => 'Iso' s t a a       -> a -> s -> t
-- ('><~') :: 'Semiring' a => 'Lens' s t a a      -> a -> s -> t
-- ('><~') :: 'Semiring' a => 'Grate' s t a a     -> a -> s -> t
-- ('><~') :: 'Semiring' a => 'Setter' s t a a    -> a -> s -> t
-- ('><~') :: 'Semiring' a => 'Traversal' s t a a -> a -> s -> t
-- @
--
(><~) :: Semiring a => ASetter s t a a -> a -> s -> t
l ><~ n = over l (>< n)
{-# INLINE (><~) #-}

-- | Replace the target(s) of a settable in a monadic state.
--
-- This is an infix version of 'assigns'.
--
-- >>> execState (do first .= 1; second .= 2) (3,4)
-- (1,2)
--
-- >>> execState (both .= 3) (1,2)
-- (3,3)
--
-- @
-- ('.=') :: 'MonadState' s m => 'Iso'' s a       -> a -> m ()
-- ('.=') :: 'MonadState' s m => 'Lens'' s a      -> a -> m ()
-- ('.=') :: 'MonadState' s m => 'Traversal'' s a -> a -> m ()
-- ('.=') :: 'MonadState' s m => 'Setter'' s a    -> a -> m ()
-- @
--
(.=) :: MonadState s m => ASetter s s a b -> b -> m ()
l .= b = State.modify (l .~ b)
{-# INLINE (.=) #-}

-- | Replace the target(s) of a settable in a monadic state.
--
-- @
-- 'assigns' :: 'MonadState' s m => 'Iso'' s a       -> a -> m ()
-- 'assigns' :: 'MonadState' s m => 'Lens'' s a      -> a -> m ()
-- 'assigns' :: 'MonadState' s m => 'Grate'' s a     -> a -> m ()
-- 'assigns' :: 'MonadState' s m => 'Setter'' s a    -> a -> m ()
-- 'assigns' :: 'MonadState' s m => 'Traversal'' s a -> a -> m ()
-- @
--
assigns :: MonadState s m => ASetter s s a b -> b -> m ()
assigns l b = State.modify (set l b)
{-# INLINE assigns #-}

-- | Map over the target(s) of a 'Setter' in a monadic state.
--
-- This is an infix version of 'modifies'.
--
-- >>> execState (do first %= (+1) ;second %= (+2)) (1,2)
-- (2,4)
--
-- >>> execState (do both %= (+1)) (1,2)
-- (2,3)
--
-- @
-- ('%=') :: 'MonadState' s m => 'Iso'' s a       -> (a -> a) -> m ()
-- ('%=') :: 'MonadState' s m => 'Lens'' s a      -> (a -> a) -> m ()
-- ('%=') :: 'MonadState' s m => 'Grate'' s a     -> (a -> a) -> m ()
-- ('%=') :: 'MonadState' s m => 'Setter'' s a    -> (a -> a) -> m ()
-- ('%=') :: 'MonadState' s m => 'Traversal'' s a -> (a -> a) -> m ()
-- @
--
(%=) :: MonadState s m => ASetter s s a b -> (a -> b) -> m ()
l %= f = State.modify (l %~ f)
{-# INLINE (%=) #-}

-- | Map over the target(s) of a 'Setter' in a monadic state.
--
-- @
-- 'modifies' :: 'MonadState' s m => 'Iso'' s a       -> (a -> a) -> m ()
-- 'modifies' :: 'MonadState' s m => 'Lens'' s a      -> (a -> a) -> m ()
-- 'modifies' :: 'MonadState' s m => 'Grate'' s a     -> (a -> a) -> m ()
-- 'modifies' :: 'MonadState' s m => 'Setter'' s a    -> (a -> a) -> m ()
-- 'modifies' :: 'MonadState' s m => 'Traversal'' s a -> (a -> a) -> m ()
-- @
--
modifies :: MonadState s m => ASetter s s a b -> (a -> b) -> m ()
modifies l f = State.modify (over l f)
{-# INLINE modifies #-}

-- | Replace the target(s) of a settable optic with 'Just' a new value.
--
-- >>> execState (do first ?= 1; second ?= 2) (Just 1, Nothing)
-- (Just 1,Just 2)
--
-- @
-- ('?=') :: 'MonadState' s m => 'Iso'' s ('Maybe' a)       -> a -> m ()
-- ('?=') :: 'MonadState' s m => 'Lens'' s ('Maybe' a)      -> a -> m ()
-- ('?=') :: 'MonadState' s m => 'Grate'' s ('Maybe' a)     -> a -> m ()
-- ('?=') :: 'MonadState' s m => 'Setter'' s ('Maybe' a)    -> a -> m ()
-- ('?=') :: 'MonadState' s m => 'Traversal'' s ('Maybe' a) -> a -> m ()
-- @
--
(?=) :: MonadState s m => ASetter s s a (Maybe b) -> b -> m ()
l ?= b = State.modify (l ?~ b)
{-# INLINE (?=) #-}

-- | Modify the target(s) of a settable optic by adding a value.
--
-- >>> execState (both <>= False) (False,True)
-- (False,True)
--
-- >>> execState (both <>= "!!!") ("hello","world")
-- ("hello!!!","world!!!")
--
-- @
-- ('<>=') :: 'MonadState' s m => 'Semigroup' a => 'Iso'' s a -> a -> m ()
-- ('<>=') :: 'MonadState' s m => 'Semigroup' a => 'Lens'' s a -> a -> m ()
-- ('<>=') :: 'MonadState' s m => 'Semigroup' a => 'Grate'' s a -> a -> m ()
-- ('<>=') :: 'MonadState' s m => 'Semigroup' a => 'Setter'' s a -> a -> m ()
-- ('<>=') :: 'MonadState' s m => 'Semigroup' a => 'Traversal'' s a -> a -> m ()
-- @
--
(<>=) :: MonadState s m => Semigroup a => ASetter' s a -> a -> m ()
l <>= a = State.modify (l <>~ a)
{-# INLINE (<>=) #-}

-- | Modify the target(s) of a settable optic by mulitiplying by a value.
--
-- >>> execState (both ><= False) (False,True)
-- (False,False)
--
-- @
-- ('><=') :: 'MonadState' s m => 'Semiring' a => 'Iso'' s a -> a -> m ()
-- ('><=') :: 'MonadState' s m => 'Semiring' a => 'Lens'' s a -> a -> m ()
-- ('><=') :: 'MonadState' s m => 'Semiring' a => 'Grate'' s a -> a -> m ()
-- ('><=') :: 'MonadState' s m => 'Semiring' a => 'Setter'' s a -> a -> m ()
-- ('><=') :: 'MonadState' s m => 'Semiring' a => 'Traversal'' s a -> a -> m ()
-- @
--
(><=) :: MonadState s m => Semiring a => ASetter' s a -> a -> m ()
l ><= a = State.modify (l ><~ a)
{-# INLINE (><=) #-}

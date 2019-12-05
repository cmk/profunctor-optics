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
  , ixsetter
  , closing
    -- * Resetter
  , Resetter
  , Resetter'
  , resetter
  , cxsetter
    -- * Optics
  , cod
  , dom
  , bound 
  , fmapped
  , contramapped
  , liftedA
  , liftedM
  , locally
  , zipped
  , cond
  , modded
  , reviewed
  , composed
  , exmapped
    -- * Primitive operators
  , over
  , ixover
  , ixoverFrom
  , under
  , cxover
  , through
    -- * Operators
  , assignA
  , set
  , ixset
  , reset
  , cxset
  , (.~)
  , (..~)
  , (%~)
  , (%%~)
  , (/~)
  , (//~)
  , (#~)
  , (##~)
  , (?~)
  , (<>~)
  , (><~)
    -- * MonadState
  , assigns
  , modifies
  , (.=)
  , (..=)
  , (%=)
  , (%%=)
  , (//=)
  , (#=)
  , (##=)
  , (?=)
  , (<>=)
  , (><=)
  , zoom
    -- * Carriers
  , ASetter
  , ASetter'
  , Star(..)
  , AResetter
  , AResetter'
  , Costar(..)
    -- * Classes
  , Representable(..)
  , Corepresentable(..)
) where

import Control.Applicative (liftA)
import Control.Exception (Exception(..))
import Control.Monad.Reader as Reader
import Control.Monad.State as State
import Control.Monad.Writer as Writer
import Data.Foldable (Foldable, foldMap)
import Data.Profunctor.Arrow
import Data.Profunctor.Optic.Import hiding ((&&&))
import Data.Profunctor.Optic.Index (Index(..), Coindex(..), trivial)
import Data.Profunctor.Optic.Type
import Data.Semiring

import qualified Control.Exception as Ex

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
-- >>> import Data.Functor.Identity
-- >>> import Data.Functor.Contravariant
-- >>> import Data.Int.Instance ()
-- >>> import Data.List.Index as LI
-- >>> import Data.IntSet as IntSet
-- >>> import Data.Set as Set
-- >>> :load Data.Profunctor.Optic
-- >>> let catchOn :: Int -> Cxprism' Int (Maybe String) String ; catchOn n = cxjust $ \k -> if k==n then Just "caught" else Nothing
-- >>> let ixtraversed :: Ixtraversal Int [a] [b] a b ; ixtraversed = ixtraversalVl itraverse
-- >>> let ixat :: Int -> Ixtraversal0' Int [a] a; ixat = inserted (\i s -> flip LI.ifind s $ \n _ -> n == i) (\i a s -> LI.modifyAt i (const a) s)

type ASetter s t a b = ARepn Identity s t a b

type ASetter' s a = ASetter s s a a

type AIxsetter i s t a b = AIxrepn Identity i s t a b

type AResetter s t a b = ACorepn Identity s t a b

type AResetter' s a = AResetter s s a a

type ACxsetter k s t a b = ACxrepn Identity k s t a b

---------------------------------------------------------------------
-- Setter
---------------------------------------------------------------------

-- | Obtain a 'Setter' from a <http://conal.net/blog/posts/semantic-editor-combinators SEC>.
--
-- To demote an optic to a semantic edit combinator, use the section @(l ..~)@ or @over l@.
--
-- >>> [("The",0),("quick",1),("brown",1),("fox",2)] & setter fmap . t21 ..~ Prelude.length
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
-- 'ixsetter' '.' 'ixover' ≡ 'id'
-- 'ixover' '.' 'ixsetter' ≡ 'id'
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
ixsetter :: ((i -> a -> b) -> s -> t) -> Ixsetter i s t a b
ixsetter f = setter $ \iab -> f (curry iab) . snd 
{-# INLINE ixsetter #-}

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
cxsetter :: ((k -> a -> t) -> s -> t) -> Cxsetter k s t a t
cxsetter f = resetter $ \kab -> const . f (flip kab)
{-# INLINE cxsetter #-}

-- | Every valid 'Grate' is a 'Setter'.
--
closing :: (((s -> a) -> b) -> t) -> Setter s t a b
closing sabt = setter $ \ab s -> sabt $ \sa -> ab (sa s)
{-# INLINE closing #-}

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
-- >>> over t21 (+1) (1,2)
-- (2,2)
--
-- >>> over t21 show (10,20)
-- ("10",20)
--
-- @
-- over :: Setter s t a b -> (a -> r) -> s -> r
-- over :: Monoid r => Fold s t a b -> (a -> r) -> s -> r
-- @
--
over :: ASetter s t a b -> (a -> b) -> s -> t
over o = (runIdentity #.) #. runStar #. o .# Star .# (Identity #. ) 
{-# INLINE over #-}

-- |
--
-- >>> ixover (ixat 1) (+) [1,2,3 :: Int]
-- [1,3,3]
--
-- >>> ixover (ixat 5) (+) [1,2,3 :: Int]
-- [1,2,3]
--
ixover :: Monoid i => AIxsetter i s t a b -> (i -> a -> b) -> s -> t
ixover o f = ixoverFrom o f mempty 
{-# INLINE ixover #-}

ixoverFrom :: AIxsetter i s t a b -> (i -> a -> b) -> i -> s -> t
ixoverFrom o f = curry (over o (uncurry f))
{-# INLINE ixoverFrom #-}

-- | Extract a SEC from a 'Resetter'.
--
-- @
-- 'under' o 'id' ≡ 'id' 
-- 'under' o f '.' 'under' o g ≡ 'under' o (f '.' g)
-- 'resetter' '.' 'under' ≡ 'id'
-- 'under' '.' 'resetter' ≡ 'id'
-- @
--
-- Note that 'under' (more properly co-/over/) is distinct from 'Data.Profunctor.Optic.Iso.reover':
--
-- >>> :t under $ wrapped @(Identity Int)
-- under $ wrapped @(Identity Int)
--   :: (Int -> Int) -> Identity Int -> Identity Int
-- >>> :t over $ wrapped @(Identity Int)
-- over $ wrapped @(Identity Int)
--   :: (Int -> Int) -> Identity Int -> Identity Int
-- >>> :t over . re $ wrapped @(Identity Int)
-- over . re $ wrapped @(Identity Int)
--   :: (Identity Int -> Identity Int) -> Int -> Int
-- >>> :t reover $ wrapped @(Identity Int)
-- reover $ wrapped @(Identity Int)
--   :: (Identity Int -> Identity Int) -> Int -> Int
--
-- Compare to the /lens-family/ <http://hackage.haskell.org/package/lens-family-2.0.0/docs/Lens-Family2.html#v:under version>.
--
under :: AResetter s t a b -> (a -> b) -> s -> t
under o = (.# Identity) #. runCostar #. o .# Costar .# (.# runIdentity)
{-# INLINE under #-}

-- |
--
-- >>> cxover (catchOn 42) (\k msg -> show k ++ ": " ++ msg) $ Just "foo"
-- Just "0: foo"
--
-- >>> cxover (catchOn 42) (\k msg -> show k ++ ": " ++ msg) Nothing
-- Nothing
--
-- >>> cxover (catchOn 0) (\k msg -> show k ++ ": " ++ msg) Nothing
-- Just "caught"
--
cxover :: Monoid k => ACxsetter k s t a b -> (k -> a -> b) -> s -> t 
cxover o f = flip (under o (flip f)) mempty
{-# INLINE cxover #-}

-- | The join of 'under' and 'over'.
--
through :: Optic (->) s t a b -> (a -> b) -> s -> t
through = id
{-# INLINE through #-}

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

-- | Modify the local environment of a 'Reader'. 
--
-- Use to lift reader actions into a larger environment:
--
-- >>> runReader ( ask & locally ..~ fst ) (1,2)
-- 1
--
locally :: Setter (ReaderT r2 m a) (ReaderT r1 m a) r1 r2
locally = setter withReaderT
{-# INLINE locally #-}

-- | TODO: Document
--
zipped :: Setter (u -> v -> a) (u -> v -> b) a b
zipped = setter ((.)(.)(.))
{-# INLINE zipped #-}

-- | Apply a function only when the given condition holds.
--
-- See also 'Data.Profunctor.Optic.Affine.predicated' & 'Data.Profunctor.Optic.Prism.filtered'.
--
cond :: (a -> Bool) -> Setter' a a
cond p = setter $ \f a -> if p a then f a else a
{-# INLINE cond #-}

-- | TODO: Document
--
modded :: (a -> Bool) -> Setter' (a -> b) b
modded p = setter $ \mods f a -> if p a then mods (f a) else f a
{-# INLINE modded #-}

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

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

infixr 4 .~, ..~, %~, %%~, /~, //~, #~, ##~, ?~, <>~, ><~

-- | Run a profunctor arrow command and set the optic targets to the result.
--
-- Similar to 'assign', except that the type of the object being modified can change.
--
-- >>> getVal1 = Right 3
-- >>> getVal2 = Right False
-- >>> action = assignA t21 (Kleisli (const getVal1)) >>> assignA t22 (Kleisli (const getVal2))
-- >>> runKleisli action ((), ())
-- Right (3,False)
--
-- @
-- 'assignA' :: 'Category' p => 'Iso' s t a b       -> 'Lenslike' p s t s b
-- 'assignA' :: 'Category' p => 'Lens' s t a b      -> 'Lenslike' p s t s b
-- 'assignA' :: 'Category' p => 'Grate' s t a b     -> 'Lenslike' p s t s b
-- 'assignA' :: 'Category' p => 'Setter' s t a b    -> 'Lenslike' p s t s b
-- 'assignA' :: 'Category' p => 'Traversal' s t a b -> 'Lenslike' p s t s b
-- @
--
assignA :: Category p => Strong p => ASetter s t a b -> Optic p s t s b 
assignA o p = arr (flip $ set o) &&& p >>> arr (uncurry id)
{-# INLINE assignA #-}

-- | Set all referenced fields to the given value.
--
-- @ 'set' l y ('set' l x a) ≡ 'set' l y a @
--
set :: ASetter s t a b -> b -> s -> t
set o b = over o (const b)
{-# INLINE set #-}

-- | Set with index. Equivalent to 'ixover' with the current value ignored.
--
-- When you do not need access to the index, then 'set' is more liberal in what it can accept.
--
-- @
-- 'set' o ≡ 'ixset' o '.' 'const'
-- @
--
-- >>> ixset (ixat 2) (2-) [1,2,3 :: Int]
-- [1,2,0]
--
-- >>> ixset (ixat 5) (const 0) [1,2,3 :: Int]
-- [1,2,3]
--
ixset :: Monoid i => AIxsetter i s t a b -> (i -> b) -> s -> t
ixset o = ixover o . (const .)
{-# INLINE ixset #-}

-- | Set all referenced fields to the given value.
--
-- @
-- 'reset' ≡ 'set' '.' 're'
-- @
-- 
reset :: AResetter s t a b -> b -> s -> t
reset o b = under o (const b)
{-# INLINE reset #-}

-- | Dual set with index. Equivalent to 'cxover' with the current value ignored.
--
-- >>> cxset (catchOn 42) show $ Just "foo"
-- Just "0"
--
-- >>> cxset (catchOn 42) show Nothing
-- Nothing
--
-- >>> cxset (catchOn 0) show Nothing
-- Just "caught"
--
cxset :: Monoid k => ACxsetter k s t a b -> (k -> b) -> s -> t 
cxset o kb = cxover o $ flip (const kb)
{-# INLINE cxset #-}

-- | TODO: Document
--
(.~) :: ASetter s t a b -> b -> s -> t
(.~) = set
{-# INLINE (.~) #-}

-- | TODO: Document
--
-- >>> Nothing & just ..~ (+1)
-- Nothing
--
(..~) :: ASetter s t a b -> (a -> b) -> s -> t
(..~) = over
{-# INLINE (..~) #-}

-- | An infix variant of 'ixset'. Dual to '#~'.
--
(%~) :: Monoid i => AIxsetter i s t a b -> (i -> b) -> s -> t
(%~) = ixset
{-# INLINE (%~) #-}

-- | An infix variant of 'ixover'. Dual to '##~'.
--
(%%~) :: Monoid i => AIxsetter i s t a b -> (i -> a -> b) -> s -> t
(%%~) = ixover
{-# INLINE (%%~) #-}

-- | An infix variant of 'reset'. Dual to '.~'.
--
(/~) :: AResetter s t a b -> b -> s -> t
(/~) = reset
{-# INLINE (/~) #-}

-- | An infix variant of 'under'. Dual to '..~'.
--
(//~) :: AResetter s t a b -> (a -> b) -> s -> t
(//~) = under
{-# INLINE (//~) #-}

-- | An infix variant of 'cxset'. Dual to '%~'.
--
(#~) :: Monoid k => ACxsetter k s t a b -> (k -> b) -> s -> t 
(#~) = cxset
{-# INLINE (#~) #-}

-- | An infix variant of 'cxover'. Dual to '%%~'.
--
-- >>> Just "foo" & catchOn 0 ##~ (\k msg -> show k ++ ": " ++ msg)
-- Just "0: foo"
--
-- >>> Nothing & catchOn 0 ##~ (\k msg -> show k ++ ": " ++ msg)
-- Just "caught"
--
(##~) :: Monoid k => ACxsetter k s t a b -> (k -> a -> b) -> s -> t 
(##~) = cxover
{-# INLINE (##~) #-}

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
-- >>> ('a', ('b', 'c')) & t22 . both ?~ 'x'
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

---------------------------------------------------------------------
-- MonadState
---------------------------------------------------------------------

infix 4 .=, ..=, %=, %%=, //=, #=, ##=, ?=, <>=, ><=

-- | Replace the target(s) of a settable in a monadic state.
--
-- @
-- 'assigns' :: 'MonadState' s m => 'Iso'' s a       -> a -> m ()
-- 'assigns' :: 'MonadState' s m => 'Lens'' s a      -> a -> m ()
-- 'assigns' :: 'MonadState' s m => 'Grate'' s a     -> a -> m ()
-- 'assigns' :: 'MonadState' s m => 'Prism'' s a     -> a -> m ()
-- 'assigns' :: 'MonadState' s m => 'Setter'' s a    -> a -> m ()
-- 'assigns' :: 'MonadState' s m => 'Traversal'' s a -> a -> m ()
-- @
--
assigns :: MonadState s m => ASetter s s a b -> b -> m ()
assigns o b = State.modify (set o b)
{-# INLINE assigns #-}

-- | Map over the target(s) of a 'Setter' in a monadic state.
--
-- @
-- 'modifies' :: 'MonadState' s m => 'Iso'' s a       -> (a -> a) -> m ()
-- 'modifies' :: 'MonadState' s m => 'Lens'' s a      -> (a -> a) -> m ()
-- 'modifies' :: 'MonadState' s m => 'Grate'' s a     -> (a -> a) -> m ()
-- 'modifies' :: 'MonadState' s m => 'Prism'' s a     -> (a -> a) -> m ()
-- 'modifies' :: 'MonadState' s m => 'Setter'' s a    -> (a -> a) -> m ()
-- 'modifies' :: 'MonadState' s m => 'Traversal'' s a -> (a -> a) -> m ()
-- @
--
modifies :: MonadState s m => ASetter s s a b -> (a -> b) -> m ()
modifies o f = State.modify (over o f)
{-# INLINE modifies #-}

-- | Replace the target(s) of a settable in a monadic state.
--
-- This is an infix version of 'assigns'.
--
-- >>> execState (do t21 .= 1; t22 .= 2) (3,4)
-- (1,2)
--
-- >>> execState (both .= 3) (1,2)
-- (3,3)
--
-- @
-- ('.=') :: 'MonadState' s m => 'Iso'' s a       -> a -> m ()
-- ('.=') :: 'MonadState' s m => 'Lens'' s a      -> a -> m ()
-- ('.=') :: 'MonadState' s m => 'Grate'' s a    -> a -> m ()
-- ('.=') :: 'MonadState' s m => 'Prism'' s a    -> a -> m ()
-- ('.=') :: 'MonadState' s m => 'Setter'' s a    -> a -> m ()
-- ('.=') :: 'MonadState' s m => 'Traversal'' s a -> a -> m ()
-- @
--
(.=) :: MonadState s m => ASetter s s a b -> b -> m ()
o .= b = State.modify (o .~ b)
{-# INLINE (.=) #-}

-- | Map over the target(s) of a 'Setter' in a monadic state.
--
-- This is an infix version of 'modifies'.
--
-- >>> execState (do just ..= (+1) ) Nothing
-- Nothing
--
-- >>> execState (do t21 ..= (+1) ;t22 ..= (+2)) (1,2)
-- (2,4)
--
-- >>> execState (do both ..= (+1)) (1,2)
-- (2,3)
--
-- @
-- ('..=') :: 'MonadState' s m => 'Iso'' s a       -> (a -> a) -> m ()
-- ('..=') :: 'MonadState' s m => 'Lens'' s a      -> (a -> a) -> m ()
-- ('..=') :: 'MonadState' s m => 'Grate'' s a     -> (a -> a) -> m ()
-- ('..=') :: 'MonadState' s m => 'Prism'' s a     -> (a -> a) -> m ()
-- ('..=') :: 'MonadState' s m => 'Setter'' s a    -> (a -> a) -> m ()
-- ('..=') :: 'MonadState' s m => 'Traversal'' s a -> (a -> a) -> m ()
-- @
--
(..=) :: MonadState s m => ASetter s s a b -> (a -> b) -> m ()
o ..= f = State.modify (o ..~ f)
{-# INLINE (..=) #-}

-- | TODO: Document 
--
(%=) :: MonadState s m => Monoid i => AIxsetter i s s a b -> (i -> b) -> m ()
o %= b = State.modify (o %~ b)

-- | TODO: Document 
--
(%%=) :: MonadState s m => Monoid i => AIxsetter i s s a b -> (i -> a -> b) -> m () 
o %%= f = State.modify (o %%~ f)
{-# INLINE (%%=) #-}

-- | TODO: Document 
--
(//=) :: MonadState s m => AResetter s s a b -> (a -> b) -> m ()
o //= f = State.modify (o //~ f)
{-# INLINE (//=) #-}

-- | TODO: Document 
--
(#=) :: MonadState s m => Monoid k => ACxsetter k s s a b -> (k -> b) -> m ()
o #= f = State.modify (o #~ f)
{-# INLINE (#=) #-}

-- | TODO: Document 
--
(##=) :: MonadState s m => Monoid k => ACxsetter k s s a b -> (k -> a -> b) -> m () 
o ##= f = State.modify (o ##~ f)
{-# INLINE (##=) #-}

-- | Replace the target(s) of a settable optic with 'Just' a new value.
--
-- >>> execState (do t21 ?= 1; t22 ?= 2) (Just 1, Nothing)
-- (Just 1,Just 2)
--
-- @
-- ('?=') :: 'MonadState' s m => 'Iso'' s ('Maybe' a)       -> a -> m ()
-- ('?=') :: 'MonadState' s m => 'Lens'' s ('Maybe' a)      -> a -> m ()
-- ('?=') :: 'MonadState' s m => 'Grate'' s ('Maybe' a)     -> a -> m ()
-- ('?=') :: 'MonadState' s m => 'Prism'' s ('Maybe' a)     -> a -> m ()
-- ('?=') :: 'MonadState' s m => 'Setter'' s ('Maybe' a)    -> a -> m ()
-- ('?=') :: 'MonadState' s m => 'Traversal'' s ('Maybe' a) -> a -> m ()
-- @
--
(?=) :: MonadState s m => ASetter s s a (Maybe b) -> b -> m ()
o ?= b = State.modify (o ?~ b)
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
-- ('<>=') :: 'MonadState' s m => 'Semigroup' a => 'Prism'' s a -> a -> m ()
-- ('<>=') :: 'MonadState' s m => 'Semigroup' a => 'Setter'' s a -> a -> m ()
-- ('<>=') :: 'MonadState' s m => 'Semigroup' a => 'Traversal'' s a -> a -> m ()
-- @
--
(<>=) :: MonadState s m => Semigroup a => ASetter' s a -> a -> m ()
o <>= a = State.modify (o <>~ a)
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
-- ('><=') :: 'MonadState' s m => 'Semiring' a => 'Prism'' s a -> a -> m ()
-- ('><=') :: 'MonadState' s m => 'Semiring' a => 'Setter'' s a -> a -> m ()
-- ('><=') :: 'MonadState' s m => 'Semiring' a => 'Traversal'' s a -> a -> m ()
-- @
--
(><=) :: MonadState s m => Semiring a => ASetter' s a -> a -> m ()
o ><= a = State.modify (o ><~ a)
{-# INLINE (><=) #-}

-- @
-- zoom :: Functor m => Lens' ta a -> StateT a m c -> StateT ta m c
-- zoom :: (Monoid c, Applicative m) => Traversal' ta a -> StateT a m c -> StateT ta m c
-- @
zoom :: Functor m => Optic' (Star (Compose m ((,) c))) ta a -> StateT a m c -> StateT ta m c
zoom o (StateT m) = StateT . out . o . into $ m
 where
  into f = Star (Compose . f)
  out (Star f) = getCompose . f

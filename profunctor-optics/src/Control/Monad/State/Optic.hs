{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}

module Control.Monad.State.Optic (
    zoom
  , use
  , reuse
  , uses 
  , reuses
  , assigns
  , modifies
  , (.=)
  , (..=)
  , (?=)
  , (<>=)
  , (><=)
  , (+=)
  , (-=)
  , (*=)
  , (&&=)
  , (||=)
) where

import Control.Monad.Reader as Reader
import Control.Monad.State as State
import Data.Profunctor.Optic
import Data.Profunctor.Optic.Import
import Data.Semiring
import Prelude (Num(..))

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XFlexibleContexts
-- >>> :set -XTypeApplications
-- >>> :set -XTupleSections
-- >>> :set -XRankNTypes
-- >>> import Control.Monad.State
-- >>> import Data.Functor.Identity
-- >>> import Data.List.Index
-- >>> :load Data.Profunctor.Optic

infix 4 ..=, .=, ?=, +=, *=, -=, <>=, ><=, &&=, ||=

-- @
-- zoom :: Functor m => Lens' ta a -> StateT a m c -> StateT ta m c
-- zoom :: (Monoid c, Applicative m) => Traversal' ta a -> StateT a m c -> StateT ta m c
-- @
zoom :: Functor m => Optic' (Star (Compose m ((,) c))) ta a -> StateT a m c -> StateT ta m c
zoom o (StateT m) = StateT . out . o . into $ m
 where
  into f = Star (Compose . f)
  out (Star f) = getCompose . f

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
-- >>> execState (do first .= 1; second .= 2) (3,4)
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
-- >>> execState (do first ..= (+1) ;second ..= (+2)) (1,2)
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

-- | Replace the target(s) of a settable optic with 'Just' a new value.
--
-- >>> execState (do first ?= 1; second ?= 2) (Just 1, Nothing)
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

(+=), (-=), (*=) :: Monad m => Num a => ASetter' s a -> a -> StateT s m ()
-- | Modify the target(s) of an optic by adding a value.
--
-- @
-- ('+=') :: ('MonadState' s m, 'Num' a) => 'Setter'' s a    -> a -> m ()
-- ('+=') :: ('MonadState' s m, 'Num' a) => 'Iso'' s a       -> a -> m ()
-- ('+=') :: ('MonadState' s m, 'Num' a) => 'Lens'' s a      -> a -> m ()
-- ('+=') :: ('MonadState' s m, 'Num' a) => 'Traversal'' s a -> a -> m ()
-- @
--
o += b = State.modify (o +~ b)
{-# INLINE (+=) #-}

-- | Modify the target(s) of an optic by subtracting a value.
--
-- @
-- ('-=') :: ('MonadState' s m, 'Num' a) => 'Setter'' s a    -> a -> m ()
-- ('-=') :: ('MonadState' s m, 'Num' a) => 'Iso'' s a       -> a -> m ()
-- ('-=') :: ('MonadState' s m, 'Num' a) => 'Lens'' s a      -> a -> m ()
-- ('-=') :: ('MonadState' s m, 'Num' a) => 'Traversal'' s a -> a -> m ()
-- @
--
o -= b = State.modify (o -~ b)
{-# INLINE (-=) #-}

-- | Modify the target(s) of an optic by multiplying by value.
--
-- @
-- ('*=') :: ('MonadState' s m, 'Num' a) => 'Setter'' s a    -> a -> m ()
-- ('*=') :: ('MonadState' s m, 'Num' a) => 'Iso'' s a       -> a -> m ()
-- ('*=') :: ('MonadState' s m, 'Num' a) => 'Lens'' s a      -> a -> m ()
-- ('*=') :: ('MonadState' s m, 'Num' a) => 'Traversal'' s a -> a -> m ()
-- @
--
o *= b = State.modify (o *~ b)
{-# INLINE (*=) #-}

(&&=), (||=) :: MonadState s m => ASetter' s Bool -> Bool -> m ()
-- | Modify the target(s) of an optic by taking their logical '&&' with a value.
--
-- >>> execState (do first &&= True; second &&= False) (True,True)
-- (True,False)
--
-- @
-- ('&&=') :: 'MonadState' s m => 'Setter'' s 'Bool'    -> 'Bool' -> m ()
-- ('&&=') :: 'MonadState' s m => 'Iso'' s 'Bool'       -> 'Bool' -> m ()
-- ('&&=') :: 'MonadState' s m => 'Lens'' s 'Bool'      -> 'Bool' -> m ()
-- ('&&=') :: 'MonadState' s m => 'Traversal'' s 'Bool' -> 'Bool' -> m ()
-- @
--
o &&= b = State.modify (o &&~ b)
{-# INLINE (&&=) #-}

-- | Modify the target(s) of an optic by taking their logical '||' with a value.
--
-- >>> execState (do first ||= True; second ||= False) (True,False)
-- (True,False)
--
-- @
-- ('||=') :: 'MonadState' s m => 'Setter'' s 'Bool'    -> 'Bool' -> m ()
-- ('||=') :: 'MonadState' s m => 'Iso'' s 'Bool'       -> 'Bool' -> m ()
-- ('||=') :: 'MonadState' s m => 'Lens'' s 'Bool'      -> 'Bool' -> m ()
-- ('||=') :: 'MonadState' s m => 'Traversal'' s 'Bool' -> 'Bool' -> m ()
-- @
--
o ||= b = State.modify (o ||~ b)
{-# INLINE (||=) #-}

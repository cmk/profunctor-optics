{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Option (
    -- * Option & Ixoption
    Option
  , option
  , ioption
  , failing
  , toOption
  , fromOption 
    -- * Optics
  , optioned
  , filtered
    -- * Primitive operators
  , withOption
  , withIxoption
    -- * Operators
  , (^?)
  , preview 
  , preuse
    -- * Indexed operators
  , ipreview
  , ipreviews
    -- * MonadUnliftIO 
  , tries
  , tries_ 
  , catches
  , catches_
  , handles
  , handles_
) where

import Control.Exception (Exception)
import Control.Monad.IO.Unlift
import Control.Monad.Reader as Reader hiding (lift)
import Control.Monad.State as State hiding (lift)
import Data.Maybe
import Data.Monoid hiding (All(..), Any(..))
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Prism (just, async)
import Data.Profunctor.Optic.Affine (affineVl, iaffineVl, is)
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.View
import qualified Control.Exception as Ex

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> :set -XRankNTypes
-- >>> import Control.Exception hiding (catches)
-- >>> import Data.Functor.Identity
-- >>> import Data.List.Index as LI
-- >>> import Data.Map as Map
-- >>> import Data.Maybe
-- >>> import Data.Monoid
-- >>> import Data.Semiring hiding (unital,nonunital,presemiring)
-- >>> import Data.Sequence as Seq
-- >>> import qualified Data.List.NonEmpty as NE
-- >>> :load Data.Profunctor.Optic
-- >>> let itraversed :: Ixtraversal Int [a] [b] a b ; itraversed = itraversalVl itraverse
-- >>> let iat :: Int -> Ixaffine' Int [a] a; iat i = iaffine' (\s -> flip LI.ifind s $ \n _ -> n==i) (\s a -> LI.modifyAt i (const a) s) 

---------------------------------------------------------------------
-- 'Option' & 'Ixoption'
---------------------------------------------------------------------

-- | Obtain a 'Option' directly.
--
-- @
-- 'option' . 'preview' ≡ id
-- 'option' ('view' o) ≡ o . 'just'
-- @
--
-- >>> preview (option . preview $ selected even) (2, "yes")
-- Just "yes"
--
-- >>> preview (option . preview $ selected even) (3, "no")
-- Nothing
--
-- >>> preview (option listToMaybe) "foo"
-- Just 'f'
--
option :: (s -> Maybe a) -> Option s a
option f = to (\s -> maybe (Left s) Right (f s)) . right'
{-# INLINE option #-}

-- | Obtain an 'Ixoption' directly.
--
ioption :: (s -> Maybe (i, a)) -> Ixoption i s a
ioption g = iaffineVl (\point f s -> maybe (point s) (uncurry f) $ g s) . coercer
{-# INLINE ioption #-}

infixl 3 `failing` -- Same as (<|>)

-- | If the first 'Option' has no focus then try the second one.
--
failing :: AOption a s a -> AOption a s a -> Option s a
failing a b = option $ \s -> maybe (preview b s) Just (preview a s)
{-# INLINE failing #-}

-- | Obtain a 'Option' from a 'View'.
--
-- @
-- 'toOption' o ≡ o . 'just'
-- 'toOption' o ≡ 'option' ('view' o)
-- @
--
toOption :: View s (Maybe a) -> Option s a
toOption = (. just)
{-# INLINE toOption #-}

-- | Obtain a 'View' from a 'Option' 
--
fromOption ::  AOption a s a -> View s (Maybe a)
fromOption = to . preview
{-# INLINE fromOption #-}

---------------------------------------------------------------------
-- Optics 
---------------------------------------------------------------------

-- | The canonical 'Option'. 
--
-- >>> [Just 1, Nothing] ^.. folded . optioned
-- [1]
--
optioned :: Option (Maybe a) a
optioned = option id
{-# INLINE optioned #-}

-- | Filter another optic.
--
-- >>> [1..10] ^.. folded . filtered even
-- [2,4,6,8,10]
--
filtered :: (a -> Bool) -> Option a a
filtered p = affineVl (\point f a -> if p a then f a else point a) . coercer
{-# INLINE filtered #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

infixl 8 ^?

-- | An infix alias for 'preview''.
--
-- @
-- ('^?') ≡ 'flip' 'preview''
-- @
--
-- Perform a safe 'head' of a 'Fold' or 'Traversal' or retrieve 'Just'
-- the result from a 'View' or 'Lens'.
--
-- When using a 'Traversal' as a partial 'Lens', or a 'Fold' as a partial
-- 'View' this can be a convenient way to extract the optional value.
--
-- >>> Left 4 ^? left'
-- Just 4
--
-- >>> Right 4 ^? left'
-- Nothing
--
(^?) :: s -> AOption a s a -> Maybe a
(^?) = flip preview
{-# INLINE (^?) #-}

-- | TODO: Document
--
preview :: MonadReader s m => AOption a s a -> m (Maybe a)
preview o = Reader.asks $ withOption o Just
{-# INLINE preview #-}

-- | TODO: Document
--
preuse :: MonadState s m => AOption a s a -> m (Maybe a)
preuse o = State.gets $ preview o
{-# INLINE preuse #-}

------------------------------------------------------------------------------
-- Indexed operators
------------------------------------------------------------------------------

-- | TODO: Document 
--
ipreview :: Monoid i => AIxoption (i , a) i s a -> s -> Maybe (i , a)
ipreview o = ipreviews o (,)
{-# INLINE ipreview #-}

-- | TODO: Document 
--
ipreviews :: Monoid i => AIxoption r i s a -> (i -> a -> r) -> s -> Maybe r
ipreviews o f = withIxoption o (\i -> Just . f i)
{-# INLINE ipreviews #-}

------------------------------------------------------------------------------
-- 'MonadUnliftIO'
------------------------------------------------------------------------------

-- | Test for synchronous exceptions that match a given optic.
--
-- In the style of 'safe-exceptions' this function rethrows async exceptions 
-- synchronously in order to preserve async behavior,
-- 
-- @
-- 'tries' :: 'MonadUnliftIO' m => 'AOption' e 'Ex.SomeException' e -> m a -> m ('Either' e a)
-- 'tries' 'exception' :: 'MonadUnliftIO' m => 'Exception' e => m a -> m ('Either' e a)
-- @
--
tries :: MonadUnliftIO m => Exception ex => AOption e ex e -> m a -> m (Either e a)
tries o a = withRunInIO $ \run -> run (Right `liftM` a) `Ex.catch` \e ->
  if is async e then throwM e else run $ maybe (throwM e) (return . Left) (preview o e)
{-# INLINE tries #-}

-- | A variant of 'tries' that returns synchronous exceptions.
--
tries_ :: MonadUnliftIO m => Exception ex => AOption e ex e -> m a -> m (Maybe a)
tries_ o a = preview right' `liftM` tries o a
{-# INLINE tries_ #-}

-- | Catch synchronous exceptions that match a given optic.
--
-- Rethrows async exceptions synchronously in order to preserve async behavior.
--
-- @
-- 'catches' :: 'MonadUnliftIO' m => 'AOption' e 'Ex.SomeException' e -> m a -> (e -> m a) -> m a
-- 'catches' 'exception' :: 'MonadUnliftIO' m => Exception e => m a -> (e -> m a) -> m a
-- @
--
-- >>> catches (only Overflow) (throwIO Overflow) (\_ -> return "caught")
-- "caught"
--
catches :: MonadUnliftIO m => Exception ex => AOption e ex e -> m a -> (e -> m a) -> m a
catches o a ea = withRunInIO $ \run -> run a `Ex.catch` \e ->
  if is async e then throwM e else run $ maybe (throwM e) ea (preview o e)
{-# INLINE catches #-}

-- | Catch synchronous exceptions that match a given optic, discarding the match.
--
-- >>> catches_ (only Overflow) (throwIO Overflow) (return "caught")
-- "caught"
--
catches_ :: MonadUnliftIO m => Exception ex => AOption e ex e -> m a -> m a -> m a
catches_ o x y = catches o x $ const y
{-# INLINE catches_ #-}

-- | Flipped variant of 'catches'.
--
-- >>> handles (only Overflow) (\_ -> return "caught") $ throwIO Overflow
-- "caught"
--
handles :: MonadUnliftIO m => Exception ex => AOption e ex e -> (e -> m a) -> m a -> m a
handles o = flip $ catches o
{-# INLINE handles #-}

-- | Flipped variant of 'catches_'.
--
-- >>> handles_ (only Overflow) (return "caught") $ throwIO Overflow
-- "caught"
--
handles_ :: MonadUnliftIO m => Exception ex => AOption e ex e -> m a -> m a -> m a
handles_ o = flip $ catches_ o
{-# INLINE handles_ #-}

throwM :: MonadIO m => Exception e => e -> m a
throwM = liftIO . Ex.throwIO
{-# INLINE throwM #-}

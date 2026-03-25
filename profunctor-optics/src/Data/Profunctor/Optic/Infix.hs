{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}

-- | Left and right carriers are characterized by their representation
-- functors ('Rep' and 'Corep'). 'Iso' sits at the top where both
-- are trivial ('Identity'). 'Adjoint' sits at the bottom where they
-- form a full adjunction (@'Corep' p ⊣ 'Rep' p@). A left-indexed
-- ('Ix') optic threads an index through the left adjoint functor
-- @(,) k@, while a right-indexed ('Cx') optic threads a coindex
-- through the right adjoint functor @(->) k@.
--
-- Infix operators for profunctor optics.
--
-- This module collects all infix operators in one place. Every operator
-- is defined in terms of a named function elsewhere in the library, so
-- users who prefer prefix style can avoid importing this module entirely.
--
-- == Operator naming system
--
-- Operators are built from a small alphabet of characters. Each character
-- indicates which class of optic or carrier the operator targets:
--
-- @
--   .   primary optic, via (->)
--   *   left adjoint optic, via 'Star' f
--   %   left indexed optic
--   \/   right adjoint optic, via 'Costar' f
--   #   right indexed optic
-- @
--
-- The structural characters indicate the /direction/ of the operation:
--
-- @
--   ^   value\/structure side (view direction, value on the left)
--   ~   modification target  (set\/over direction)
--   =   monadic state        (stateful set\/over direction)
-- @
--
-- Single vs doubled middle character distinguishes set vs over:
--
-- @
--            set              over
--   (->)    (.~)             (..~)
--   Star    (*~)             (**~)   = 'traverseOf'
--   Ix      (%~)             (%%~)   = 'ixover'
--   Costar  (\/~)             (\/\/~)   = 'cotraverseOf'
--   Cx      (#~)             (##~)   = 'cxover'
-- @
--
-- View operators use @^@ on the left:
--
-- @
--            view             fold\/toList       preview
--   (->)    (^.)             (^..)             (^?)
--   Star    (^*)             (^**)
--   Ix      (^%)             (^%%)
--   Costar  (^\/)             (^\/\/)
--   Cx      (^#)             (^##)
-- @
--
-- For ternary operators (@^*@, @^**@), use '&' to pass the structure:
--
-- @
-- myStruct '&' optic '^**' effectfulFn
-- @
--
-- == Fixity
--
-- @
--   infixl 8  ^., ^?, ^.., ^*, ^**, ^%, ^%%, ^/, ^//, ^#, ^##
--   infixr 4  .~, ..~, *~, **~, %~, %%~, /~, //~, #~, ##~
--   infix  4  .=, ..=
-- @
--
module Data.Profunctor.Optic.Infix (
    -- * Re-exports
    (&)
    -- * Adjoint (via ->)
    -- ** View
  , (^?), (^.), (^..)
    -- ** Set\/over
  , (.~), (..~)
    -- * Left Adjoint (Star)
    -- ** View
  , (^*), (^**)
    -- ** Set\/over
  , (*~), (**~)
    -- * Left Adjoint (Ix)
    -- ** View
  , (^%), (^%%)
    -- ** Set\/over
  , (%~), (%%~)
    -- * Right Adjoint (Costar)
    -- ** View
  , (^/), (^//)
    -- ** Set\/over
  , (/~), (//~)
    -- * Right Adjoint (Cx)
    -- ** View
  , (^#), (^##)
    -- ** Set\/over
  , (#~), (##~)
    -- * MTL
  , (.=), (..=)
) where

import Control.Monad.State (MonadState)
import Data.Function ((&))
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Import

import qualified Data.Profunctor.Optic.View as V
import qualified Data.Profunctor.Optic.Fold as F
import qualified Data.Profunctor.Optic.Setter as S
import qualified Data.Profunctor.Optic.Index as C
import qualified Data.Profunctor.Optic.Traversal as T

---------------------------------------------------------------------
-- Fixity declarations
---------------------------------------------------------------------

infixl 8  ^., ^?, ^.., ^*, ^**, ^%, ^%%, ^/, ^//, ^#, ^##
infixr 4  .~, ..~, *~, **~, %~, %%~, /~, //~, #~, ##~
infix  4  .=, ..=

---------------------------------------------------------------------
-- Adjoint (via ->)
---------------------------------------------------------------------

-- | Preview through an affine fold.
--
-- @s '^?' o ≡ 'F.preview' o s@
--
(^?) :: s -> AFold0 a s a -> Maybe a
(^?) = flip F.preview
{-# INLINE (^?) #-}

-- | View through an optic.
--
-- @s '^.' o ≡ 'V.view' o s@
--
(^.) :: s -> AView a s a -> a
(^.) = flip V.view
{-# INLINE (^.) #-}

-- | Fold to a list.
--
-- @s '^..' o ≡ 'F.toListOf' o s@
--
(^..) :: s -> AFold (Endo [a]) s a -> [a]
(^..) = flip F.toListOf
{-# INLINE (^..) #-}

-- | Set via a primary optic.
--
-- @o '.~' b ≡ over o (const b)@
--
(.~) :: AAdjoint s t a b -> b -> s -> t
(.~) o b = o (const b)
{-# INLINE (.~) #-}

-- | Over (map) via a primary optic.
--
-- @o '..~' f ≡ over o f@
--
(..~) :: AAdjoint s t a b -> (a -> b) -> s -> t
(..~) = id
{-# INLINE (..~) #-}

---------------------------------------------------------------------
-- Left Adjoint (Star)
---------------------------------------------------------------------

-- | Effectful view via 'Star'.
--
-- @s '&' o '^*' fb ≡ 'T.traverseOf' o (const fb) s@
--
(^*) :: ATraversal f s t a b -> f b -> s -> f t
(^*) o b = o ^** const b
{-# INLINE (^*) #-}

-- | Effectful over via 'Star'. Equivalent to 'T.traverseOf'.
--
-- @s '&' o '^**' f ≡ 'T.traverseOf' o f s@
--
(^**) :: ATraversal f s t a b -> (a -> f b) -> s -> f t
(^**) o = runStar #. o .# Star
{-# INLINE (^**) #-}

-- | Effectful set via 'Star'.
--
-- @o '*~' fb ≡ o '**~' const fb@
--
(*~) :: ATraversal f s t a b -> f b -> s -> f t
(*~) o b = o **~ const b
{-# INLINE (*~) #-}

-- | Effectful over via 'Star'. Equivalent to 'T.traverseOf'.
--
-- @o '**~' f ≡ 'T.traverseOf' o f@
--
(**~) :: ATraversal f s t a b -> (a -> f b) -> s -> f t
(**~) o = runStar #. o .# Star
{-# INLINE (**~) #-}

---------------------------------------------------------------------
-- Left Adjoint (Ix)
---------------------------------------------------------------------

-- | View with index.
--
-- @s '^%' o ≡ 'V.ixview' o s@
--
(^%) :: Monoid k => s -> AIxview k s a -> (k, a)
(^%) = flip V.ixview
{-# INLINE (^%) #-}

-- | Fold to an indexed list.
--
-- @s '^%%' o ≡ 'F.ixtoListOf' o s@
--
(^%%) :: Monoid k => s -> AIxfold (Endo [(k, a)]) k s a -> [(k, a)]
(^%%) = flip F.ixtoListOf
{-# INLINE (^%%) #-}

-- | Indexed set.
--
-- @o '%~' f ≡ 'C.ixover' o (const . f)@
--
(%~) :: Monoid i => AIxadjoint i s t a b -> (i -> b) -> s -> t
(%~) o = C.ixover o . (const .)
{-# INLINE (%~) #-}

-- | Indexed over.
--
-- @o '%%~' f ≡ 'C.ixover' o f@
--
(%%~) :: Monoid i => AIxadjoint i s t a b -> (i -> a -> b) -> s -> t
(%%~) = C.ixover
{-# INLINE (%%~) #-}

---------------------------------------------------------------------
-- Right Adjoint (Costar)
---------------------------------------------------------------------

-- | Review: build a structure from a value.
--
-- @o '^/' b ≡ 'V.review' o b@
--
(^/) :: ACoview t b -> b -> t
(^/) = V.review
{-# INLINE (^/) #-}

-- | Co-dual fold.
--
-- @o '^//' b ≡ 'F.cofoldOfA' o b@
--
(^//) :: Coapplicative f => ACofold (f b) t b -> f b -> t
(^//) = F.cofoldOfA
{-# INLINE (^//) #-}

-- | Co-dual set via 'Costar'.
--
-- @o '/~' b ≡ o '//~' const b@
--
(/~) :: ACotraversal f s t a b -> b -> f s -> t
(/~) o b = o //~ const b
{-# INLINE (/~) #-}

-- | Co-dual over via 'Costar'. Equivalent to 'T.cotraverseOf'.
--
-- @o '//~' f ≡ 'T.cotraverseOf' o f@
--
(//~) :: ACotraversal f s t a b -> (f a -> b) -> f s -> t
(//~) o = runCostar #. o .# Costar
{-# INLINE (//~) #-}

---------------------------------------------------------------------
-- Right Adjoint (Cx)
---------------------------------------------------------------------

-- | Coindexed review.
--
-- @o '^#' b ≡ 'V.cxview' o b@
--
(^#) :: ACxview k t b -> b -> (k -> t)
(^#) = V.cxview
{-# INLINE (^#) #-}

-- | Coindexed cofold.
--
-- @o '^##' f r ≡ 'F.cxfoldMapOf' o f r@
--
(^##) :: Monoid k => ACxfold r k t b -> (k -> r -> b) -> r -> t
(^##) = F.cxfoldMapOf
{-# INLINE (^##) #-}

-- | Coindexed set.
--
-- @o '#~' f ≡ 'C.cxover' o (const . f)@
--
(#~) :: Monoid i => ACxadjoint i s t a b -> (i -> b) -> s -> t
(#~) o = C.cxover o . (const .)
{-# INLINE (#~) #-}

-- | Coindexed over.
--
-- @o '##~' f ≡ 'C.cxover' o f@
--
(##~) :: Monoid i => ACxadjoint i s t a b -> (i -> a -> b) -> s -> t
(##~) = C.cxover
{-# INLINE (##~) #-}

---------------------------------------------------------------------
-- MTL
---------------------------------------------------------------------

-- | Set in a 'Control.Monad.State.MonadState' context.
--
-- @o '.=' b ≡ 'S.assigns' o b@
--
(.=) :: MonadState s m => AAdjoint s s a b -> b -> m ()
(.=) = S.assigns
{-# INLINE (.=) #-}

-- | Over in a 'Control.Monad.State.MonadState' context.
--
-- @o '..=' f ≡ 'S.modifies' o f@
--
(..=) :: MonadState s m => AAdjoint s s a b -> (a -> b) -> m ()
(..=) = S.modifies
{-# INLINE (..=) #-}

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
--   .   (one dot\/circle)   primary optic, via (->)
--   *   (one star\/circle)  primary optic, via 'Star' f
--   %   (two circles)       indexed primary optic
--   \/   (one slash)         co-dual optic, via 'Costar' f
--   #   (two slashes)       indexed co-dual optic
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
--   (.~)    set       (..~)    over
--   (*~)    starSet   (**~)    starOver   (= 'traverseOf')
--   (%~)    ixset     (%%~)    ixover
--   (\/~)    coset     (\/\/~)    coover     (= 'cotraverseOf')
--   (#~)    cxset     (##~)    cxover
-- @
--
-- View operators use @^@ on the left:
--
-- @
--   (^.)    view              (^..)   toList        (^?)   preview
--   (^%)    ixview            (^%%)   ixtoList
--   (^\/)    review            (^\/\/)   colist
--   (^#)    rxview
-- @
--
-- State operators use @=@ instead of @~@:
--
-- @
--   (.=)    assigns           (..=)   modifies
-- @
--
-- Composition operators for indexed optics:
--
-- @
--   (%)     indexed composition
--   (#)     coindexed composition
-- @
--
-- == Fixity
--
-- Fixities are chosen to be consistent with the @lens@ library:
--
-- @
--   infixl 8  ^., ^?, ^.., ^%, ^%%, ^/, ^//, ^#, ^##
--   infixr 4  .~, ..~, *~, **~, %~, %%~, /~, //~, #~, ##~
--   infix  4  .=, ..=
--   infixr 9  %, #
-- @
--
-- This ensures that @s '^.' optic1 '.' optic2@ and @optic '.~' b '$' s@
-- parse correctly, and indexed composition binds tighter than view.
--
module Data.Profunctor.Optic.Infix (
    -- * Operators
    (^?)
    -- ** Basic view
  , (^.), (^..)
    -- ** Indexed view
  , (^%), (^%%)
    -- ** Basic set\/over
  , (.~), (..~)
    -- ** Indexed set\/over
  , (%~), (%%~)
    -- ** Effectful set\/over
  , (*~), (**~)
    -- * Dual Operators
    -- ** Basic view
  , (^/), (^//)
    -- ** Indexed view
  , (^#)
  , (^##)
    -- ** Indexed set\/over
  , (#~), (##~)
    -- ** Effectful set\/over
  , (/~), (//~)
    -- * MTL
  , (.=), (..=)
) where

import Control.Monad.State (MonadState)
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Import

import qualified Data.Profunctor.Optic.View as V
import qualified Data.Profunctor.Optic.Fold as F
import qualified Data.Profunctor.Optic.Setter as S
import qualified Data.Profunctor.Optic.Index as C

---------------------------------------------------------------------
-- Fixity declarations
---------------------------------------------------------------------

infixl 8  ^., ^?, ^.., ^%, ^%%, ^/, ^//, ^#, ^##
infixr 4  .~, ..~, *~, **~, %~, %%~, /~, //~, #~, ##~
infix  4  .=, ..=

---------------------------------------------------------------------
-- View (primary)
---------------------------------------------------------------------

-- | Preview through an affine fold.
--
-- @s '^?' o ≡ 'F.preview' o s@
--
(^?) :: s -> AFold0 a s a -> Maybe a
(^?) = flip F.preview
{-# INLINE (^?) #-}

-- $view
--
-- View operators extract or fold over the focus of an optic.
-- The @^@ character always appears on the value\/structure side.
--
-- @
--            view             toList           preview
--   (->)    (^.)  'V.view'    (^..)  'F.toListOf'   (^?)  'F.preview'
--   Ix      (^%)  'V.ixview'  (^%%)  'F.ixtoListOf'
--   Re      (^/)  'V.review'  (^//)  'F.cofoldOfA'
--   Cx      (^#)  'V.cxview'  (^##)  'F.cxfoldMapOf'
-- @

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

---------------------------------------------------------------------
-- View (indexed)
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

---------------------------------------------------------------------
-- Set / over (primary, via ->)
---------------------------------------------------------------------

-- $setover
--
-- Set and over operators follow a uniform pattern: a single middle
-- character denotes __set__ (replace the focus), while a doubled middle
-- character denotes __over__ (map a function over the focus).
--
-- @
--            set                   over
--   (->)    (.~)  'S.set'          (..~)  'C.over'
--   Star    (*~)               (**~)  'traverseOf'
--   Ix      (%~)  'S.ixset'        (%%~)  'S.ixsets'
--   Costar  (\/~)               (\/\/~)  'cotraverseOf'
--   Cx      (#~)  'S.cxset'        (##~)  'S.cxsets'
-- @

-- | Set via a primary optic.
--
-- @o '.~' b ≡ 'S.set' o b@
--
(.~) :: AAdjoint s t a b -> b -> s -> t
(.~) o b = o (const b)
{-# INLINE (.~) #-}

-- | Over (map) via a primary optic.
--
-- @o '..~' f ≡ 'C.over' o f@
--
(..~) :: AAdjoint s t a b -> (a -> b) -> s -> t
(..~) = id
{-# INLINE (..~) #-}

---------------------------------------------------------------------
-- Set / over (indexed)
---------------------------------------------------------------------

-- | Indexed set.
--
-- @o '%~' f ≡ 'S.ixset' o f@
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
-- Set / over (primary, via Star)
---------------------------------------------------------------------

-- | Effectful set via 'Star'.
--
-- @o '*~' b ≡ \\s -> 'Data.Profunctor.Types.runStar' (o ('Data.Profunctor.Types.Star' (const b))) s@
--
(*~) :: ATraversal f s t a b -> f b -> s -> f t
(*~) o b = o **~ const b
{-# INLINE (*~) #-}

-- | Effectful over via 'Star'. Equivalent to 'Data.Profunctor.Optic.Traversal.traverseOf'.
--
-- @o '**~' f ≡ 'Data.Profunctor.Optic.Traversal.traverseOf' o f@
--
(**~) :: ATraversal f s t a b -> (a -> f b) -> s -> f t
(**~) o = runStar #. o .# Star
{-# INLINE (**~) #-}

---------------------------------------------------------------------
-- View (Re-dual)
---------------------------------------------------------------------

-- | Review (Re-dual of view): build a structure from a value.
-- See "Data.Profunctor.Optic.Dual" for the Re\/Co duality.
--
-- Accepts any optic with a 'Tagged' carrier ('AReview'), including
-- 'Coview', 'Review', 'Prism', 'Iso', and 'Grate' optics.
--
-- @o '^/' b ≡ 'V.review' o b@
--
(^/) :: AReview t b -> b -> t
(^/) = V.review
{-# INLINE (^/) #-}

-- | Co-dual fold to a list.
--
-- @o '^//' b ≡ 'F.cofoldOfA' o b@
--
(^//) :: Coapplicative f => ACofold (f b) t b -> f b -> t
(^//) = F.cofoldOfA
{-# INLINE (^//) #-}

-- | Coindexed review: build a coindexed value.
--
-- This is the only coindexed Re-dual view infix. There is no
-- @rxview@ infix because the @Rx@ coindex threads via @(k, -)@ on
-- the left of the profunctor, which 'Tagged' discards. See 'V.cxview'.
--
-- @o '^#' b ≡ 'V.cxview' o b@
--
(^#) :: ACxview k t b -> b -> (k -> t)
(^#) = V.cxview
{-# INLINE (^#) #-}

-- | Coindexed cofold: apply a coindexed observation to build a result.
--
-- @o '^##' f r ≡ 'F.cxfoldMapOf' o f r@
--
(^##) :: Monoid k => ACxfold r k t b -> (k -> r -> b) -> r -> t
(^##) = F.cxfoldMapOf
{-# INLINE (^##) #-}

---------------------------------------------------------------------
-- Set / over (indexed co-dual)
---------------------------------------------------------------------

-- | Indexed co-dual set.
--
-- @o '#~' f ≡ 'S.cxset' o f@
--
(#~) :: Monoid i => ACxadjoint i s t a b -> (i -> b) -> s -> t
(#~) o = C.cxover o . (const .)
{-# INLINE (#~) #-}

-- | Indexed co-dual over.
--
-- @o '##~' f ≡ 'C.cxover' o f@
--
(##~) :: Monoid i => ACxadjoint i s t a b -> (i -> a -> b) -> s -> t
(##~) = C.cxover
{-# INLINE (##~) #-}

---------------------------------------------------------------------
-- Set / over (co-dual, via Costar)
---------------------------------------------------------------------

-- | Co-dual set via 'Costar'.
--
-- @o '\/~' b ≡ (o '\/\/~' const b)@
--
(/~) :: ACotraversal f s t a b -> b -> f s -> t
(/~) o b = o //~ const b
{-# INLINE (/~) #-}

-- | Co-dual over via 'Costar'. Equivalent to 'Data.Profunctor.Optic.Traversal.cotraverseOf'.
--
-- @o '\/\/~' f ≡ 'Data.Profunctor.Optic.Traversal.cotraverseOf' o f@
--
(//~) :: ACotraversal f s t a b -> (f a -> b) -> f s -> t
(//~) o = runCostar #. o .# Costar
{-# INLINE (//~) #-}

---------------------------------------------------------------------
-- State
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

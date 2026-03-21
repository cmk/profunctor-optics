{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}

-- | Infix operators for profunctor optics.
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
--   (*~)    starSet   (**~)    starOver   (= 'traverses')
--   (%~)    ixset     (%%~)    ixover
--   (\/~)    coset     (\/\/~)    coover     (= 'cotraverses')
--   (#~)    cxset     (##~)    cxover
-- @
--
-- View operators use @^@ on the left:
--
-- @
--   (^.)    view              (^..)   toList        (^?)   preview
--   (^%)    ixview            (^%%)   ixtoList
--   (^\/)    review            (^\/\/)   colist
--   (^#)    cxreview
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
--   infixl 8  ^., ^?, ^.., ^%, ^%%, ^/, ^//, ^#
--   infixr 4  .~, ..~, *~, **~, %~, %%~, /~, //~, #~, ##~
--   infix  4  .=, ..=
--   infixr 9  %, #
-- @
--
-- This ensures that @s '^.' optic1 '.' optic2@ and @optic '.~' b '$' s@
-- parse correctly, and indexed composition binds tighter than view.
--
module Data.Profunctor.Optic.Infix (
    -- * View (primary)
    (^.), (^?), (^..)
    -- * View (indexed)
  , (^%), (^%%)
    -- * View (co-dual)
  , (^/), (^//), (^#)
    -- * Set\/over (primary)
  , (.~), (..~)
    -- * Set\/over (Star)
  , (*~), (**~)
    -- * Set\/over (indexed)
  , (%~), (%%~)
    -- * Set\/over (co-dual)
  , (/~), (//~)
    -- * Set\/over (indexed co-dual)
  , (#~), (##~)
    -- * State
  , (.=), (..=)
    -- * Composition
  , (%), (#)
) where

import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.Import

import qualified Data.Profunctor.Optic.View as V
import qualified Data.Profunctor.Optic.Fold as F
import qualified Data.Profunctor.Optic.Setter as S
import qualified Data.Profunctor.Optic.Combinator as C

---------------------------------------------------------------------
-- Fixity declarations
---------------------------------------------------------------------

infixl 8  ^., ^?, ^.., ^%, ^%%, ^/, ^//, ^#
infixr 4  .~, ..~, *~, **~, %~, %%~, /~, //~, #~, ##~
infix  4  .=, ..=
infixr 9  %, #

---------------------------------------------------------------------
-- View (primary)
---------------------------------------------------------------------

-- | View through an optic.
--
-- @s '^.' o ≡ 'V.view' o s@
--
(^.) :: s -> AView a s a -> a
(^.) = flip V.view
{-# INLINE (^.) #-}

-- | Preview through an affine fold.
--
-- @s '^?' o ≡ 'F.preview' o s@
--
(^?) :: s -> AFold0 a s a -> Maybe a
(^?) = flip F.preview
{-# INLINE (^?) #-}

-- | Fold to a list.
--
-- @s '^..' o ≡ 'F.lists' o s@
--
(^..) :: s -> AFold (Endo [a]) s a -> [a]
(^..) = flip F.lists
{-# INLINE (^..) #-}

---------------------------------------------------------------------
-- View (indexed)
---------------------------------------------------------------------

-- | View with index.
--
-- @s '^%' o ≡ 'V.ixview' o s@
--
(^%) :: Monoid k => s -> AIxview k s a -> (Maybe k, a)
(^%) = flip V.ixview
{-# INLINE (^%) #-}

-- | Fold to an indexed list.
--
-- @s '^%%' o ≡ 'F.ixlists' o s@
--
(^%%) :: Monoid k => s -> AIxfold (Endo [(k, a)]) k s a -> [(k, a)]
(^%%) = flip F.ixlists
{-# INLINE (^%%) #-}

---------------------------------------------------------------------
-- View (co-dual)
---------------------------------------------------------------------

-- | Review (co-dual view): build a structure from a value.
--
-- @o '^/' b ≡ 'V.review' o b@
--
(^/) :: AReview t b -> b -> t
(^/) = V.review
{-# INLINE (^/) #-}

-- | Co-dual fold to a list.
--
-- @o '^//' b ≡ 'F.cofoldsa' o b@
--
(^//) :: Coapplicative f => ACofold (f b) t b -> f b -> t
(^//) = F.cofoldsa
{-# INLINE (^//) #-}

-- | Indexed co-dual view (indexed review).
--
-- @o '^#' b ≡ 'V.cxreview' o b@
--
(^#) :: ACxreview k t b -> b -> (k -> t)
(^#) = V.cxreview
{-# INLINE (^#) #-}

---------------------------------------------------------------------
-- Set / over (primary, via ->)
---------------------------------------------------------------------

-- | Set via a primary optic.
--
-- @o '.~' b ≡ 'S.set' o b@
--
(.~) :: Optic (->) s t a b -> b -> s -> t
(.~) = S.set
{-# INLINE (.~) #-}

-- | Over (map) via a primary optic.
--
-- @o '..~' f ≡ 'C.over' o f@
--
(..~) :: Optic (->) s t a b -> (a -> b) -> s -> t
(..~) = C.over
{-# INLINE (..~) #-}

---------------------------------------------------------------------
-- Set / over (primary, via Star)
---------------------------------------------------------------------

-- | Effectful set via 'Star'.
--
-- @o '*~' b ≡ \\s -> 'Data.Profunctor.Types.runStar' (o ('Data.Profunctor.Types.Star' (const b))) s@
--
(*~) :: Optic (Star f) s t a b -> f b -> s -> f t
(*~) o b = o **~ const b
{-# INLINE (*~) #-}

-- | Effectful over via 'Star'. Equivalent to 'Data.Profunctor.Optic.Traversal.traverses'.
--
-- @o '**~' f ≡ 'Data.Profunctor.Optic.Traversal.traverses' o f@
--
(**~) :: Optic (Star f) s t a b -> (a -> f b) -> s -> f t
(**~) o = runStar #. o .# Star
{-# INLINE (**~) #-}

---------------------------------------------------------------------
-- Set / over (indexed)
---------------------------------------------------------------------

-- | Indexed set.
--
-- @o '%~' f ≡ 'S.ixset' o f@
--
(%~) :: Monoid i => Ixoptic (->) i s t a b -> (i -> b) -> s -> t
(%~) = S.ixset
{-# INLINE (%~) #-}

-- | Indexed over.
--
-- @o '%%~' f ≡ 'S.ixover' o f@
--
(%%~) :: Monoid i => Ixoptic (->) i s t a b -> (i -> a -> b) -> s -> t
(%%~) = S.ixsets
{-# INLINE (%%~) #-}

---------------------------------------------------------------------
-- Set / over (co-dual, via Costar)
---------------------------------------------------------------------

-- | Co-dual set via 'Costar'.
--
-- @o '\/~' b ≡ (o '\/\/~' const b)@
--
(/~) :: Optic (Costar f) s t a b -> b -> f s -> t
(/~) o b = o //~ const b
{-# INLINE (/~) #-}

-- | Co-dual over via 'Costar'. Equivalent to 'Data.Profunctor.Optic.Traversal.cotraverses'.
--
-- @o '\/\/~' f ≡ 'Data.Profunctor.Optic.Traversal.cotraverses' o f@
--
(//~) :: Optic (Costar f) s t a b -> (f a -> b) -> f s -> t
(//~) o = runCostar #. o .# Costar
{-# INLINE (//~) #-}

---------------------------------------------------------------------
-- Set / over (indexed co-dual)
---------------------------------------------------------------------

-- | Indexed co-dual set.
--
-- @o '#~' f ≡ 'S.cxset' o f@
--
(#~) :: Monoid i => Cxoptic (->) i s t a b -> (i -> b) -> s -> t
(#~) = S.cxset
{-# INLINE (#~) #-}

-- | Indexed co-dual over.
--
-- @o '##~' f ≡ 'S.cxover' o f@
--
(##~) :: Monoid i => Cxoptic (->) i s t a b -> (i -> a -> b) -> s -> t
(##~) = S.cxsets
{-# INLINE (##~) #-}

---------------------------------------------------------------------
-- State
---------------------------------------------------------------------

-- | Set in a 'Control.Monad.State.MonadState' context.
--
-- @o '.=' b ≡ 'S.assigns' o b@
--
(.=) :: MonadState s m => Optic (->) s s a b -> b -> m ()
(.=) = S.assigns
{-# INLINE (.=) #-}

-- | Over in a 'Control.Monad.State.MonadState' context.
--
-- @o '..=' f ≡ 'S.modifies' o f@
--
(..=) :: MonadState s m => Optic (->) s s a b -> (a -> b) -> m ()
(..=) = S.modifies
{-# INLINE (..=) #-}

---------------------------------------------------------------------
-- Composition
---------------------------------------------------------------------

-- | Indexed optic composition, accumulating indices via 'Monoid'.
--
(%) :: Monoid i => Representable p => Ixoptic p i c1 c2 b1 b2 -> Ixoptic p i b1 b2 a1 a2 -> Ixoptic p i c1 c2 a1 a2
(%) = (C.%)
{-# INLINE (%) #-}

-- | Coindexed optic composition, accumulating indices via 'Monoid'.
--
(#) :: Monoid i => Corepresentable p => Cxoptic p i c1 c2 b1 b2 -> Cxoptic p i b1 b2 a1 a2 -> Cxoptic p i c1 c2 a1 a2
(#) = (C.#)
{-# INLINE (#) #-}

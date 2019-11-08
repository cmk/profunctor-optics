module Data.Profunctor.Optic.View where

import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Prelude
import Control.Monad.Reader as Reader
import Control.Monad.Writer as Writer hiding (Sum(..))
import Control.Monad.State as State hiding (StateT(..))

---------------------------------------------------------------------
-- 'View' & 'Review'
---------------------------------------------------------------------

-- | Build a 'View' from an arbitrary function.
--
-- @
-- 'to' f '.' 'to' g ≡ 'to' (g '.' f)
-- a '^.' 'to' f ≡ f a
-- @
--
-- >>> ("hello","world") ^. to snd
-- "world"
--
-- >>> 5 ^. to succ
-- 6
--
-- >>> (0, -5) ^. second . to abs
-- 5
--
-- @
-- 'to' :: (s -> a) -> 'View' s a
-- @
--
to :: (s -> a) -> PrimView s t a b
to f = coercer . lmap f
{-# INLINE to #-}

-- | Build a 'Review' from an arbitrary function.
--
-- @
-- 'from' ≡ 're' . 'to'
-- @
--
-- >>> (from Prelude.length) # [1,2,3]
-- 3
--
-- @
-- 'from' :: (b -> t) -> 'Review' t b
-- @
--
from :: (b -> t) -> PrimReview s t a b 
from f = coercel . rmap f
{-# INLINE from #-}

-- ^ @
-- 'toBoth' :: 'View' s a -> 'View' s b -> 'View' s (a, b)
-- @
--
toBoth :: AView s a1 -> AView s a2 -> PrimView s t (a1 , a2) b
toBoth l r = to (view l &&& view r)
{-# INLINE toBoth #-}

-- | TODO: Document
--
fromBoth :: AReview t1 b -> AReview t2 b -> PrimReview s (t1 , t2) a b
fromBoth l r = from (review l &&& review r)
{-# INLINE fromBoth #-}

-- | TODO: Document
--
toEither :: AView s1 a -> AView s2 a -> PrimView (s1 + s2) t a b
toEither l r = to (view l ||| view r)
{-# INLINE toEither #-}

-- | TODO: Document
--
fromEither :: AReview t b1 -> AReview t b2 -> PrimReview s t a (b1 + b2)
fromEither l r = from (review l ||| review r)
{-# INLINE fromEither #-}

-- ^ @
-- 'cloneView' :: 'AView' s a -> 'View' s a
-- 'cloneView' :: 'Monoid' a => 'AView' s a -> 'Fold' s a
-- @
--
cloneView :: AView s a -> PrimView s s a a
cloneView = to . view
{-# INLINE cloneView #-}

-- | TODO: Document
--
cloneReview :: AReview t b -> PrimReview t t b b
cloneReview = from . review
{-# INLINE cloneReview #-}

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | Map each part of a structure viewed to a SEC.
--
-- @
-- 'Data.Foldable.foldMap' = 'viewOf' 'folding''
-- 'viewOf' ≡ 'views'
-- @
--
-- >>> viewOf both id (["foo"], ["bar", "baz"])
-- ["foo","bar","baz"]
--
-- @
-- 'viewOf' ::                  'Iso'' s a        -> (a -> r) -> s -> r
-- 'viewOf' ::                  'Lens'' s a       -> (a -> r) -> s -> r
-- 'viewOf' :: 'Monoid' r    => 'Prism'' s a      -> (a -> r) -> s -> r
-- 'viewOf' :: 'Monoid' r    => 'Traversal'' s a  -> (a -> r) -> s -> r
-- 'viewOf' :: 'Monoid' r    => 'Traversal0'' s a -> (a -> r) -> s -> r
-- 'viewOf' :: 'Semigroup' r => 'Traversal1'' s a -> (a -> r) -> s -> r
-- 'viewOf' :: 'Monoid' r    => 'Fold' s a        -> (a -> r) -> s -> r
-- 'viewOf' :: 'Semigroup' r => 'Fold1' s a       -> (a -> r) -> s -> r
-- 'viewOf' ::                  'AView' s a       -> (a -> r) -> s -> r
-- @
--
viewOf :: Optic' (FoldRep r) s a -> (a -> r) -> s -> r
viewOf = between ((getConst .) . runStar) (Star . (Const . ))
{-# INLINE viewOf #-}

-- | TODO: Document
--
reviewOf :: Optic' (CofoldRep r) t b -> (r -> b) -> r -> t
reviewOf = between ((. Const) . runCostar) (Costar . (. getConst))
{-# INLINE reviewOf #-}

---------------------------------------------------------------------
-- Common 'View's and 'Review's
---------------------------------------------------------------------

-- | TODO: Document
--
coercedr :: PrimView a x a y
coercedr = coercer
{-# INLINE coercedr #-}

-- | TODO: Document
--
coercedl :: PrimReview x b y b
coercedl = coercel
{-# INLINE coercedl #-}

-- | Build a constant-valued (index-preserving) 'PrimView' from an arbitrary value.
--
-- @
-- 'like' a '.' 'like' b ≡ 'like' b
-- a '^.' 'like' b ≡ b
-- a '^.' 'like' b ≡ a '^.' 'to' ('const' b)
-- @
--
-- This can be useful as a second case 'failing' a 'Fold'
-- e.g. @foo `failing` 'like' 0@
--
like :: a -> PrimView s t a b
like = to . const
{-# INLINE like #-}

-- | Build a constant-valued (index-preserving) 'PrimReview' from an arbitrary value.
--
-- @
-- 'relike' a '.' 'relike' b ≡ 'relike' a
-- 'relike' a '#' b ≡ a
-- 'relike' a '#' b ≡ 'from' ('const' a) '#' b
-- @
--
relike :: t -> PrimReview s t a b
relike = from . const
{-# INLINE relike #-}

---------------------------------------------------------------------
-- Derived operators
---------------------------------------------------------------------

infixl 8 ^.

-- | TODO: Document
--
(^.) :: s -> AView s a -> a
(^.) = flip view
{-# INLINE ( ^. ) #-}

infixr 8 #

-- | An infix alias for 'review'. Dual to '^.'.
--
-- @
-- 'from' f # x ≡ f x
-- l # x ≡ x '^.' 're' l
-- @
--
-- This is commonly used when using a 'Prism' as a smart constructor.
--
-- >>> lefteft # 4
-- Left 4
--
-- But it can be used for any 'Prism'
--
-- >>> base 16 # 123
-- "7b"
--
-- @
-- (#) :: 'Iso''      s a -> a -> s
-- (#) :: 'Prism''    s a -> a -> s
-- (#) :: 'Review'    s a -> a -> s
-- (#) :: 'Equality'' s a -> a -> s
-- @
--
(#) :: AReview t b -> b -> t
o # b = review o b
{-# INLINE ( # ) #-}

-- ^ @
-- 'view o ≡ foldMapOf o id'
-- 'review'  ≡ 'view'  '.' 're'
-- 'reviews' ≡ 'views' '.' 're'
-- @
--
view :: MonadReader s m => AView s a -> m a
view = (`views` id)
{-# INLINE view #-}

-- ^ @
-- 'review o ≡ cofoldMapOf o id'
-- @
--
review :: MonadReader b m => AReview t b -> m t
review = (`reviews` id) 
{-# INLINE review #-}

-- ^ @
-- 'views o f ≡ foldMapOf o f'
-- @
views :: MonadReader s m => Optic' (FoldRep r) s a -> (a -> r) -> m r
views o f = Reader.asks $ viewOf o f
{-# INLINE views #-}

-- | This can be used to turn an 'Iso' or 'Prism' around and 'view' a value (or the current environment) through it the other way,
-- applying a function.
--
-- @
-- 'reviews' ≡ 'views' '.' 're'
-- 'reviews' ('from' f) g ≡ g '.' f
-- @
--
-- >>> reviews lefteft isRight "mustard"
-- False
--
-- >>> reviews (from succ) (*2) 3
-- 8
--
-- Usually this function is used in the @(->)@ 'Monad' with a 'Prism' or 'Iso', in which case it may be useful to think of
-- it as having one of these more restricted type signatures:
--
-- @
-- 'reviews' :: 'Iso'' s a   -> (s -> r) -> a -> r
-- 'reviews' :: 'Prism'' s a -> (s -> r) -> a -> r
-- @
--
-- However, when working with a 'Monad' transformer stack, it is sometimes useful to be able to 'review' the current environment, in which case
-- it may be beneficial to think of it as having one of these slightly more liberal type signatures:
--
-- @
-- 'reviews' :: 'MonadReader' a m => 'Iso'' s a   -> (s -> r) -> m r
-- 'reviews' :: 'MonadReader' a m => 'Prism'' s a -> (s -> r) -> m r
-- @
-- ^ @
-- 'reviews o f ≡ cofoldMapOf o f'
-- @
--
reviews :: MonadReader r m => ACofold r t b -> (r -> b) -> m t
reviews o f = Reader.asks $ reviewOf o f 
{-# INLINE reviews #-}

---------------------------------------------------------------------
-- 'MonadState' and 'MonadWriter'
---------------------------------------------------------------------

-- | TODO: Document
--
use :: MonadState s m => AView s a -> m a
use o = State.gets (view o)
{-# INLINE use #-}

-- | Extracts the portion of a log that is focused on by a 'View'. 
--
-- Given a 'Fold' or a 'Traversal', then a monoidal summary of the parts 
-- of the log that are visited will be returned.
--
-- @
-- 'listening' :: 'MonadWriter' w m             => 'View' w u     -> m a -> m (a, u)
-- 'listening' :: 'MonadWriter' w m             => 'Lens'' w u      -> m a -> m (a, u)
-- 'listening' :: 'MonadWriter' w m             => 'Iso'' w u       -> m a -> m (a, u)
-- 'listening' :: ('MonadWriter' w m, 'Monoid' u) => 'Fold' w u       -> m a -> m (a, u)
-- 'listening' :: ('MonadWriter' w m, 'Monoid' u) => 'Traversal'' w u -> m a -> m (a, u)
-- 'listening' :: ('MonadWriter' w m, 'Monoid' u) => 'Prism'' w u     -> m a -> m (a, u)
-- @
listening :: MonadWriter w m => AView w u -> m a -> m (a, u)
listening l m = do
  (a, w) <- Writer.listen m
  return (a, view l w)
{-# INLINE listening #-}

-- | TODO: Document
--
listenings :: MonadWriter w m => Optic' (FoldRep v) w u -> (u -> v) -> m a -> m (a, v)
listenings l uv m = do
  (a, w) <- listen m
  return (a, views l uv w)
{-# INLINE listenings #-}

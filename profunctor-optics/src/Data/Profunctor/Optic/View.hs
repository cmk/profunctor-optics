module Data.Profunctor.Optic.View where

import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Prelude
import Data.Profunctor.Optic.Prism (_Just)
import Control.Exception (Exception(..))
import GHC.Conc (ThreadId)
import qualified UnliftIO.Exception as Ux

import Control.Monad.Reader as Reader
import Control.Monad.Writer as Writer hiding (Sum(..))
import Control.Monad.State as State hiding (StateT(..))

---------------------------------------------------------------------
-- 'View'
---------------------------------------------------------------------

-- | Build a 'View' from an arbitrary function.
--
-- @
-- 'to' f '.' 'to' g ≡ 'to' (g '.' f)
-- @
--
-- @
-- a '^.' 'to' f ≡ f a
-- @
--
-- >>> ("hello","world") ^. to snd
-- "world"
--
-- >>> 5 ^. to succ
-- 6
--
-- >>> (0, -5) ^. _2 . to abs
-- 5
--
-- @
-- 'to' :: (s -> a) -> 'View' s a
-- @
--
to :: (s -> a) -> PrimView s t a b
to f = coercer . lmap f
{-# INLINE to #-}

-- | Convert a function into a 'Review'.
--  Analagous to 'to' for 'View'.
--
-- @
-- 'unto' :: (b -> t) -> 'PrimReview' s t a b
-- @
--
-- @
-- 'unto' = 'un' . 'to'
-- @
--
unto :: (b -> t) -> PrimReview s t a b 
unto f = coercel . rmap f

-- | Turn a 'View' around to get a 'Review'
--
-- @
-- 'un' = 'unto' . 'view'
-- 'unto' = 'un' . 'to'
-- @
--
-- >>> un (to length) # [1,2,3]
-- 3
un :: AView s a -> PrimReview b a t s
un = unto . (`views` id)

-- @
-- 'toBoth' :: 'AView' s a -> 'AView' s b -> 'View' s (a, b)
-- @
--
toBoth :: AView s a1 -> AView s a2 -> PrimView s t (a1 , a2) b
toBoth l r = to (view l &&& view r)

-- | TODO: Document
--
untoBoth :: AReview t1 b -> AReview t2 b -> PrimReview s (t1 , t2) a b
untoBoth l r = unto (review l &&& review r)

-- | TODO: Document
--
toEither :: AView s1 a -> AView s2 a -> PrimView (s1 + s2) t a b
toEither l r = to (view l ||| view r)

-- | TODO: Document
--
untoEither :: AReview t b1 -> AReview t b2 -> PrimReview s t a (b1 + b2)
untoEither l r = unto (review l ||| review r)

-- @
-- 'cloneView' :: 'AView' s a -> 'View' s a
-- 'cloneView' :: 'Monoid' a => 'AView' s a -> 'Fold' s a
-- @
cloneView :: AView s a -> PrimView s s a a
cloneView = to . view

-- | TODO: Document
--
cloneReview :: AReview t b -> PrimReview t t b b
cloneReview = unto . review

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | Map each part of a structure viewed through a 'Lens', 'View',
-- 'Fold' or 'Traversal' to a monoid and combine the results.
--
-- >>> viewOf both id (["foo"], ["bar", "baz"])
-- ["foo","bar","baz"]
--
-- @
-- 'Data.Foldable.foldMap' = 'viewOf' 'folded'
-- @
--
-- @
-- 'viewOf' ≡ 'views'
-- @
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
viewOf = between (dstar getConst) (ustar Const)

-- | TODO: Document
--
reviewOf :: Optic' (CofoldRep r) t b -> (r -> b) -> r -> t
reviewOf = between (dcostar Const) (ucostar getConst)

---------------------------------------------------------------------
-- Common 'View's and 'Review's
---------------------------------------------------------------------

-- | TODO: Document
--
coercingr :: View a a 
coercingr = coercer

-- | TODO: Document
--
coercingl :: Review b b
coercingl = coercel

-- | TODO: Document
--
_1' :: PrimView (a , c) (b , c) a b
_1' = to fst

-- | TODO: Document
--
_2' :: PrimView (c , a) (c , b) a b
_2' = to snd

-- | TODO: Document
--
_L' :: PrimReview (a + c) (b + c) a b
_L' = coercel . rmap Left

-- | TODO: Document
--
_R' :: PrimReview (c + a) (c + b) a b
_R' = coercel . rmap Right

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

-- | Build a constant-valued (index-preserving) 'PrimReview' from an arbitrary value.
--
-- @
-- 'relike' a '.' 'relike' b ≡ 'relike' a
-- 'relike' a '#' b ≡ a
-- 'relike' a '#' b ≡ 'unto' ('const' a) '#' b
-- @
--
relike :: t -> PrimReview s t a b
relike t = unto (const t)

---------------------------------------------------------------------
-- Derived operators
---------------------------------------------------------------------

infixl 8 ^.

-- | TODO: Document
--
(^.) :: s -> AView s a -> a
(^.) = flip view

infixr 8 #

-- | An infix alias for 'review'. Dual to '^.'.
--
-- @
-- 'unto' f # x ≡ f x
-- l # x ≡ x '^.' 're' l
-- @
--
-- This is commonly used when using a 'Prism' as a smart constructor.
--
-- >>> _Left # 4
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
-- @
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
-- 'reviews' ('unto' f) g ≡ g '.' f
-- @
--
-- >>> reviews _Left isRight "mustard"
-- False
--
-- >>> reviews (unto succ) (*2) 3
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
-- Exception handling
---------------------------------------------------------------------

-- | Throw an 'Exception' described by a 'Prism'. Exceptions may be thrown from
-- purely functional code, but may only be caught within the 'IO' 'Monad'.
--
-- @
-- 'throws' o ≡ 'throwIO' . 'review' o
-- @
--
-- @
-- 'throws' o e \`seq\` x  ≡ 'throws' o e
-- @
--
throws :: MonadIO m => Exception t => AReview t b -> b -> m r
throws o = Ux.throwIO . review o

-- | Similar to 'throws' but specialised for the common case of
--   error constructors with no arguments.
--
-- @
-- data MyError = Foo | Bar
-- makePrisms ''MyError
-- 'throws_' _Foo :: 'MonadError' MyError m => m a
-- @
throws_ :: MonadIO m => Exception t => AReview t () -> m r
throws_ l = throws l ()

-- | 'throwsTo' raises an 'Exception' specified by a 'Prism' in the target thread.
--
-- @
-- 'throwsTo' thread o ≡ 'throwTo' thread . 'review' o
-- @
--
throwsTo :: MonadIO m => Exception t => ThreadId -> AReview t b -> b -> m ()
throwsTo tid o = Ux.throwTo tid . review o

---------------------------------------------------------------------
-- 'MonadState' and 'MonadWriter'
---------------------------------------------------------------------

-- | TODO: Document
--
use :: MonadState s m => AView s a -> m a
use o = State.gets (view o)

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

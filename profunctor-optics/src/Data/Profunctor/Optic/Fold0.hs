module Data.Profunctor.Optic.Fold0 where

import Control.Monad.Reader as Reader
import Control.Monad.State as State
import Data.Maybe
import Data.Profunctor.Optic.Prelude
import Data.Profunctor.Optic.Prism (_Just)
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.View (to)

---------------------------------------------------------------------
-- 'Fold0'
---------------------------------------------------------------------

-- | Build a 'Fold0' from an arbitrary function.
--
-- @
-- 'fold0' ('toMaybeOf' o) ≡ o
-- 'fold0' ('view' o) ≡ o . '_Just'
-- @
--
-- >>> [Just 1, Nothing] ^.. folding id . fold0 id
-- [1]
--
fold0 :: (s -> Maybe a) -> Fold0 s a
fold0 f = to (\s -> maybe (Left s) Right (f s)) . pright
{-# INLINE fold0 #-}

infixl 3 `failing` -- Same as (<|>)

-- | Try the first 'Fold0'. If it returns no entry, try the second one.
--
failing :: AFold0 a s a -> AFold0 a s a -> Fold0 s a
failing a b = fold0 $ \s -> maybe (preview b s) Just (preview a s)
{-# INLINE failing #-}

-- | Build a 'Fold0' from a 'View'.
--
-- @
-- 'toFold0' o ≡ o . '_Just'
-- 'toFold0' o ≡ 'fold0' ('view' o)
-- @
--
toFold0 :: View s (Maybe a) -> Fold0 s a
toFold0 = (. _Just)
{-# INLINE toFold0 #-}

-- | Build a 'View' from a 'Fold0' 
--
fromFold0 :: Monoid a => AFold0 a s a -> View s (Maybe a)
fromFold0 = to . preview
{-# INLINE fromFold0 #-}

---------------------------------------------------------------------
-- 'Fold0Rep'
---------------------------------------------------------------------

newtype Fold0Rep r a b = Fold0Rep { runFold0Rep :: a -> Maybe r }

type AFold0 r s a = Optic' (Fold0Rep r) s a

instance Functor (Fold0Rep r a) where
  fmap _ (Fold0Rep p) = Fold0Rep p

instance Contravariant (Fold0Rep r a) where
  contramap _ (Fold0Rep p) = Fold0Rep p

instance Profunctor (Fold0Rep r) where
  dimap f _ (Fold0Rep p) = Fold0Rep (p . f)

instance Choice (Fold0Rep r) where
  left' (Fold0Rep p) = Fold0Rep (either p (const Nothing))
  right' (Fold0Rep p) = Fold0Rep (either (const Nothing) p)

instance Cochoice (Fold0Rep r) where
  unleft  (Fold0Rep k) = Fold0Rep (k . Left)
  unright (Fold0Rep k) = Fold0Rep (k . Right)

instance Strong (Fold0Rep r) where
  first' (Fold0Rep p) = Fold0Rep (p . fst)
  second' (Fold0Rep p) = Fold0Rep (p . snd)

instance Sieve (Fold0Rep r) (Pre r) where
  sieve = (Pre .) . runFold0Rep

instance Representable (Fold0Rep r) where
  type Rep (Fold0Rep r) = Pre r
  tabulate = Fold0Rep . (getPre .)
  {-# INLINE tabulate #-}

-- | 'Pre' is 'Maybe' with a phantom type variable.
--
newtype Pre a b = Pre { getPre :: Maybe a } deriving (Eq, Ord, Show)

instance Functor (Pre a) where fmap _ (Pre p) = Pre p

instance Contravariant (Pre a) where contramap _ (Pre p) = Pre p

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | TODO: Document
--
previewOf :: Optic' (Fold0Rep r) s a -> (a -> Maybe r) -> s -> Maybe r
previewOf = between runFold0Rep Fold0Rep

-- | TODO: Document
--
toMaybeOf :: AFold0 a s a -> s -> Maybe a
toMaybeOf = flip previewOf Just

---------------------------------------------------------------------
-- Derived operators
---------------------------------------------------------------------

-- | TODO: Document
--
preview :: MonadReader s m => AFold0 a s a -> m (Maybe a)
preview o = Reader.asks $ toMaybeOf o

-- | TODO: Document
--
preuse :: MonadState s m => AFold0 a s a -> m (Maybe a)
preuse o = State.gets $ preview o

infixl 8 ^?

-- | An infix variant of 'preview''.
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
-- >>> Left 4 ^? _L
-- Just 4
--
-- >>> Right 4 ^? _L
-- Nothing
--
(^?) :: s -> AFold0 a s a -> Maybe a
s ^? o = toMaybeOf o s

-- | Check to see if this 'Fold0' doesn't match.
--
-- >>> is _Just Nothing
-- False
--
is :: AFold0 a s a -> s -> Bool
is k s = isJust (preview k s)
{-# INLINE is #-}

-- | Check to see if this 'Fold0' doesn't match.
--
-- >>> isnt _Just Nothing
-- True
--
isnt :: AFold0 a s a -> s -> Bool
isnt k s = not (isJust (preview k s))
{-# INLINE isnt #-}

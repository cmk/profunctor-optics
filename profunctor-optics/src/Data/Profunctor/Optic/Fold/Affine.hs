module Data.Profunctor.Optic.Fold.Affine where

import Data.Semigroup
import Data.Profunctor.Optic.Type 
import Data.Profunctor.Optic.Prelude

import Data.Profunctor.Optic.Getter (view, to)
import Data.Profunctor.Optic.Prism (_Just)
import Data.Foldable (traverse_)
--import Data.Functor.Const (Const(..))
--import Data.Profunctor.Optic.Fold.Monoid (foldlOf')

import Control.Monad ((<=<))
import Control.Monad.Reader as Reader
import Control.Monad.State as State

import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE

import Data.Profunctor.Optic.Setter
import Data.Profunctor.Optic.Traversal.Affine

import Data.Maybe

---------------------------------------------------------------------
-- 'Pre'
---------------------------------------------------------------------

-- | 'Pre' is 'Maybe' with a phantom type variable.
--
-- 
-- Star (Pre r) a b has Strong. Also Choice & Traversing when r is a Semigroup.
-- idea: 
newtype Pre a b = Pre { getPre :: Maybe a } deriving (Eq, Ord, Show)

instance Functor (Pre a) where fmap f (Pre p) = Pre p

instance Contravariant (Pre a) where contramap f (Pre p) = Pre p

--instance Semigroup a => Apply (Pre a) where (Pre pbc) <.> (Pre pb) = Pre $ pbc <> pb
{-
instance Monoid a => Applicative (Pre a) where

    pure _ = Pre mempty

    --(<*>) = (<.>)

    (Pre pbc) <*> (Pre pb) = Pre $ pbc <> pb
-}
newtype Fold0Rep r a b = Fold0Rep { runFold0Rep :: a -> Maybe r }

instance Profunctor (Fold0Rep r) where
  dimap f _ (Fold0Rep p) = Fold0Rep (p . f)

instance Sieve (Fold0Rep r) (Pre r) where
  sieve = (Pre .) . runFold0Rep

instance Representable (Fold0Rep r) where
  type Rep (Fold0Rep r) = Pre r
  tabulate = Fold0Rep . (getPre .)
  {-# INLINE tabulate #-}

instance Choice (Fold0Rep r) where
    right' (Fold0Rep p) = Fold0Rep (either (const Nothing) p)

instance Cochoice (Fold0Rep r) where
  unleft  (Fold0Rep k) = Fold0Rep (k . Left)
  unright (Fold0Rep k) = Fold0Rep (k . Right)

instance Strong (Fold0Rep r) where
    first' (Fold0Rep p) = Fold0Rep (p . fst)

---------------------------------------------------------------------
-- 'Fold0'
---------------------------------------------------------------------

type AFold0 r s a = Optic' (Fold0Rep r) s a
-- TODO remove or replace w First, causes unwanted semigroup interactions
--type AFold0 a s a = AFold0 a s a 

{-

Fold0 laws:

affine_fold_complete :: Fold0 s a -> Bool
affine_fold_complete o = tripping o $ afolding (toMaybeOf o)
-}

-- | Build a 'Fold0' from an arbitrary function.
--
-- >>> [Just 1, Nothing] ^.. folding id . afolding id
-- [1]
--
-- @
-- 'afolding' ('view' o) ≡ o . '_Just'
-- @
--
afolding :: (s -> Maybe a) -> Fold0 s a
afolding f = rcoerce . lmap (\s -> maybe (Left s) Right (f s)) . right'

-- | Build a 'Fold0' from an affine 'Getter'.
--
-- @
-- 'toFold0' o ≡ o . '_Just'
-- 'toFold0' o ≡ 'afolding' ('view' o)
-- @
--
toFold0 :: Getter s (Maybe a) -> Fold0 s a
toFold0 = (. _Just)

-- | TODO: Document
--
fromFold0 :: Monoid a => AFold0 a s a -> Getter s (Maybe a)
fromFold0 = to . preview

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

previewOf :: Optic' (Fold0Rep r) s a -> (a -> Maybe r) -> s -> Maybe r
previewOf = between runFold0Rep Fold0Rep

toMaybeOf :: AFold0 a s a -> s -> Maybe a
toMaybeOf = flip previewOf Just

---------------------------------------------------------------------
-- Derived operators
---------------------------------------------------------------------

preview :: MonadReader s m => AFold0 a s a -> m (Maybe a)
preview o = Reader.asks $ toMaybeOf o

preuse :: MonadState s m => AFold0 a s a -> m (Maybe a)
preuse o = State.gets $ preview o

infixl 8 ^?

-- | An infix variant of 'preview''.
--
-- Performs a safe 'head' of a 'Fold' or 'Traversal' or retrieve 'Just' 
-- the result from a 'Getter' or 'Lens'.
--
-- When using a 'Traversal' as a partial 'Lens', or a 'Fold' as a partial 
-- 'Getter' this can be a convenient way to extract the optional value.
--
--
-- >>> Left 4 ^? _L
-- Just 4
--
-- >>> Right 4 ^? _L
-- Nothing
--
-- @
-- ('^?') ≡ 'flip' 'preview''
-- @
--
-- @
-- ('^?') :: s -> 'Getter' s a         -> 'Maybe' a
-- ('^?') :: s -> 'Fold' s a         -> 'Maybe' a
-- ('^?') :: s -> 'Lens'' s a        -> 'Maybe' a
-- ('^?') :: s -> 'Prism'' s a       -> 'Maybe' a
-- ('^?') :: s -> 'Traversal0'' s a      -> 'Maybe' a
-- ('^?') :: s -> 'Iso'' s a         -> 'Maybe' a
-- ('^?') :: s -> 'Traversal'' s a   -> 'Maybe' a
-- @
--
(^?) :: s -> AFold0 a s a -> Maybe a
s ^? o = toMaybeOf o s

-- | Filter result(s) of a fold that don't satisfy a predicate.
afiltered :: (a -> Bool) -> Fold0 a a
afiltered p = atraversing $ \point f a -> if p a then f a else point a

-- | Try the first 'Fold0'. If it returns no entry, try the second one.
--
-- >>> preview (ix 1 . re _L `afailing` ix 2 . re _R) [0,1,2,3]
-- Just (Left 1)
--
-- >>> preview (ix 42 . re _L `afailing` ix 2 . re _R) [0,1,2,3]
-- Just (Right 2)
--
afailing :: AFold0 a s a -> AFold0 a s a -> Fold0 s a
afailing a b = afolding $ \s -> maybe (preview b s) Just (preview a s)
infixl 3 `afailing` -- Same as (<|>)
{-# INLINE afailing #-}

-- | Check to see if this 'Fold0' doesn't match.
--
-- >>> isnt _Just Nothing
-- True
--
isnt :: AFold0 a s a -> s -> Bool
isnt k s = not (isJust (preview k s))
{-# INLINE isnt #-}


{-
-- | Find the innermost focus of a `Fold` that satisfies a predicate, if there is any.
--
findOf :: AFold0 (Endo (Maybe a)) s a -> (a -> Bool) -> s -> Maybe a
findOf o f =
  foldrOf o (\a -> maybe (if f a then Just a else Nothing) Just) Nothing

-- | The maximum of all foci of a `Fold`, if there is any.
--
maxOf :: Ord a => Optic' (FoldRep (Endo (Maybe a))) s a -> s -> Maybe a
maxOf o = foldrOf o (\a -> Just . maybe a (max a)) Nothing

-- | The minimum of all foci of a `Fold`, if there is any.
--
minOf :: Ord a => Optic' (FoldRep (Endo (Maybe a))) s a -> s -> Maybe a
minOf o = foldrOf o (\a -> Just . maybe a (min a)) Nothing
-}


{-

-- | Obtain the minimum element (if any) targeted by a 'Fold', 'Traversal', 'Lens', 'Iso'
-- or 'Getter' according to a user supplied 'Ordering'.
--
-- In the interest of efficiency, This operation has semantics more strict than strictly necessary.
--
-- >>> minimumByOf traverse' (compare `on` length) ["mustard","relish","ham"]
-- Just "ham"
--
-- @
-- 'minimumBy' cmp ≡ 'Data.Maybe.fromMaybe' ('error' \"empty\") '.' 'minimumByOf' 'folded' cmp
-- @
--
-- @
-- 'minimumByOf' :: 'Getter' s a     -> (a -> a -> 'Ordering') -> s -> 'Maybe' a
-- 'minimumByOf' :: 'Fold' s a       -> (a -> a -> 'Ordering') -> s -> 'Maybe' a
-- 'minimumByOf' :: 'Iso'' s a       -> (a -> a -> 'Ordering') -> s -> 'Maybe' a
-- 'minimumByOf' :: 'Lens'' s a      -> (a -> a -> 'Ordering') -> s -> 'Maybe' a
-- 'minimumByOf' :: 'Traversal'' s a -> (a -> a -> 'Ordering') -> s -> 'Maybe' a
-- @
minimumByOf :: AFold0 (Endo (Endo (Maybe a))) s a -> (a -> a -> Ordering) -> s -> Maybe a
minimumByOf o cmp = foldlOf' o mf Nothing where
  mf Nothing y = Just $! y
  mf (Just x) y = Just $! if cmp x y == GT then y else x
{-# INLINE minimumByOf #-}

-- | The 'findOf' function takes a 'Lens' (or 'Getter', 'Iso', 'Fold', or 'Traversal'),
-- a predicate and a structure and returns the leftmost element of the structure
-- matching the predicate, or 'Nothing' if there is no such element.
--
-- >>> findOf each even (1,3,4,6)
-- Just 4
--
-- >>> findOf folded even [1,3,5,7]
-- Nothing
--
-- @
-- 'findOf' :: 'Getter' s a     -> (a -> 'Bool') -> s -> 'Maybe' a
-- 'findOf' :: 'Fold' s a       -> (a -> 'Bool') -> s -> 'Maybe' a
-- 'findOf' :: 'Iso'' s a       -> (a -> 'Bool') -> s -> 'Maybe' a
-- 'findOf' :: 'Lens'' s a      -> (a -> 'Bool') -> s -> 'Maybe' a
-- 'findOf' :: 'Traversal'' s a -> (a -> 'Bool') -> s -> 'Maybe' a
-- @
--
-- @
-- 'Data.Foldable.find' ≡ 'findOf' 'folded'
-- 'ifindOf' o ≡ 'findOf' o '.' 'Indexed'
-- @
--
-- A simpler version that didn't permit indexing, would be:
--
-- @
-- 'findOf' :: 'AFold' ('Endo' ('Maybe' a)) s a -> (a -> 'Bool') -> s -> 'Maybe' a
-- 'findOf' o p = 'foldrOf' o (\a y -> if p a then 'Just' a else y) 'Nothing'
-- @
findOf :: AFold0 (Endo (Maybe a)) s a -> (a -> Bool) -> s -> Maybe a
findOf o f = foldrOf o (\a y -> if f a then Just a else y) Nothing
{-# INLINE findOf #-}

-- | The 'findMOf' function takes a 'Lens' (or 'Getter', 'Iso', 'Fold', or 'Traversal'),
-- a monadic predicate and a structure and returns in the monad the leftmost element of the structure
-- matching the predicate, or 'Nothing' if there is no such element.
--
-- >>>  findMOf each ( \x -> print ("Checking " ++ show x) >> return (even x)) (1,3,4,6)
-- "Checking 1"
-- "Checking 3"
-- "Checking 4"
-- Just 4
--
-- >>>  findMOf each ( \x -> print ("Checking " ++ show x) >> return (even x)) (1,3,5,7)
-- "Checking 1"
-- "Checking 3"
-- "Checking 5"
-- "Checking 7"
-- Nothing
--
-- @
-- 'findMOf' :: ('Monad' m, 'Getter' s a)     -> (a -> m 'Bool') -> s -> m ('Maybe' a)
-- 'findMOf' :: ('Monad' m, 'Fold' s a)       -> (a -> m 'Bool') -> s -> m ('Maybe' a)
-- 'findMOf' :: ('Monad' m, 'Iso'' s a)       -> (a -> m 'Bool') -> s -> m ('Maybe' a)
-- 'findMOf' :: ('Monad' m, 'Lens'' s a)      -> (a -> m 'Bool') -> s -> m ('Maybe' a)
-- 'findMOf' :: ('Monad' m, 'Traversal'' s a) -> (a -> m 'Bool') -> s -> m ('Maybe' a)
-- @
--
-- @
-- 'findMOf' 'folded' :: (Monad m, Foldable f) => (a -> m Bool) -> f a -> m (Maybe a)
-- 'ifindMOf' o ≡ 'findMOf' o '.' 'Indexed'
-- @
--
-- A simpler version that didn't permit indexing, would be:
--
-- @
-- 'findMOf' :: Monad m => 'AFold' ('Endo' (m ('Maybe' a))) s a -> (a -> m 'Bool') -> s -> m ('Maybe' a)
-- 'findMOf' o p = 'foldrOf' o (\a y -> p a >>= \x -> if x then return ('Just' a) else y) $ return 'Nothing'
-- @
findMOf :: Monad m => AFold0 (Endo (m (Maybe a))) s a -> (a -> m Bool) -> s -> m (Maybe a)
findMOf o f = foldrOf o (\a y -> f a >>= \r -> if r then return (Just a) else y) $ return Nothing
{-# INLINE findMOf #-}

-- | The 'lookupOf' function takes a 'Fold' (or 'Getter', 'Traversal',
-- 'Lens', 'Iso', etc.), a key, and a structure containing key/value pairs.
-- It returns the first value corresponding to the given key. This function
-- generalizes 'lookup' to work on an arbitrary 'Fold' instead of lists.
--
-- >>> lookupOf folded 4 [(2, 'a'), (4, 'b'), (4, 'c')]
-- Just 'b'
--
-- >>> lookupOf each 2 [(2, 'a'), (4, 'b'), (4, 'c')]
-- Just 'a'
--
-- @
-- 'lookupOf' :: 'Eq' k => 'Fold' s (k,v) -> k -> s -> 'Maybe' v
-- @
lookupOf :: Eq k => AFold0 (Endo (Maybe v)) s (k,v) -> k -> s -> Maybe v
lookupOf o k = foldrOf o (\(k',v) next -> if k == k' then Just v else next) Nothing
{-# INLINE lookupOf #-}
-}

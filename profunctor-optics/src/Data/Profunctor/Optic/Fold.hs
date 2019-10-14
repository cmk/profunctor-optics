module Data.Profunctor.Optic.Fold where

import Control.Monad ((<=<))
import Data.DList (DList)
import Data.Foldable (traverse_)
import Data.Functor.Foldable (Recursive, Base, fold)
import Data.Monoid
import Data.Profunctor.Optic.Getter (view, to)
import Data.Profunctor.Optic.Prelude
import Data.Profunctor.Optic.Type 
import qualified Data.DList as DL

---------------------------------------------------------------------
-- 'Fold'
---------------------------------------------------------------------

type AFold r s a = Monoid r => FoldLike r s a

{-

A 'Fold' can interpret 'a' in a monoid so long as 's' can also be interpreted that way.

Fold laws:

fold_complete :: Fold s a -> Bool
fold_complete o = tripping o $ folding (toListOf o)
-}


-- | Obtain a 'Fold' by lifting an operation that returns a 'Foldable' result.
--
-- This can be useful to lift operations from @Data.List@ and elsewhere into a 'Fold'.
--
-- >>> [1,2,3,4] ^.. folding tail
-- [2,3,4]
--
folding :: Foldable f => (s -> f a) -> Fold s a
folding f = rcoerce . lmap f . lift traverse_
{-# INLINE folding #-}

-- | Obtain a 'Fold' using a 'Traversable' functor.
--
-- @
-- 'folded' f ≡ 'over' 'traverse' . 'to' f
-- @
--
folded :: Traversable f => (s -> a) -> Fold (f s) a
folded f = lift traverse . to f

-- recursing :: FoldLike r (Mu []) [r]
recursing :: Recursive s => FoldLike a s (Base s a)
recursing = foldLike fold

foldLike :: ((a -> r) -> s -> r) -> FoldLike r s a
foldLike = between (ustar Const) (dstar getConst)

foldLike' :: Foldable f => AFold r (f a) a
foldLike' = foldLike foldMap

cloneFold :: FoldLike a s a -> Fold s a
cloneFold = to . view

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | Map each part of a structure viewed through a 'Lens', 'Getter',
-- 'Fold' or 'Traversal' to a monoid and combine the results.
--
-- >>> foldMapOf both id (["foo"], ["bar", "baz"])
-- ["foo","bar","baz"]
--
--
-- @
-- 'foldMapOf' ≡ 'views'
-- @
--
-- @
-- 'foldMapOf' ::                  'Iso'' s a        -> (a -> r) -> s -> r
-- 'foldMapOf' ::                  'Lens'' s a       -> (a -> r) -> s -> r
-- 'foldMapOf' :: 'Monoid' r    => 'Prism'' s a      -> (a -> r) -> s -> r
-- 'foldMapOf' :: 'Monoid' r    => 'Traversal'' s a  -> (a -> r) -> s -> r
-- 'foldMapOf' :: 'Monoid' r    => 'Affine'' s a     -> (a -> r) -> s -> r
-- 'foldMapOf' :: 'Monoid' r    => 'Fold' s a        -> (a -> r) -> s -> r
-- 'foldMapOf' :: 'Semigroup' r => 'Fold1' s a       -> (a -> r) -> s -> r
-- @
--
foldMapOf :: FoldLike r s a -> (a -> r) -> s -> r
foldMapOf = between (dstar getConst) (ustar Const)

-- | Collects the foci of a `Fold` into a list.
--
toListOf :: FoldLike (DList a) s a -> s -> [a]
toListOf o = flip DL.apply [] . foldMapOf o DL.singleton 

-- | 
foldOf :: FoldLike a s a -> s -> a
foldOf = flip foldMapOf id

-- @
-- toPureOf :: Fold s a -> s -> [a]
-- toPureOf :: (Applicative f, Monoid (f a)) => Fold s a -> s -> f a
-- toPureOf :: Applicative f => Setter s t a b -> s -> f a
-- @
toPureOf :: Applicative f => FoldLike (f a) s a -> s -> f a
toPureOf o = foldMapOf o pure

infixl 8 ^..

-- | A convenient infix (flipped) version of 'toListOf'.
--
-- >>> [[1,2],[3]] ^.. id
-- [[[1,2],[3]]]
-- >>> [[1,2],[3]] ^.. traversed
-- [[1,2],[3]]
-- >>> [[1,2],[3]] ^.. traversed . traversed
-- [1,2,3]
--
-- >>> (1,2) ^.. both
-- [1,2]
--
-- @
-- 'Data.Foldable.toList' xs ≡ xs '^..' 'folded'
-- ('^..') ≡ 'flip' 'toListOf'
-- @
--
-- @
-- ('^..') :: s -> 'Getter' s a     -> [a]
-- ('^..') :: s -> 'Fold' s a       -> [a]
-- ('^..') :: s -> 'Lens'' s a      -> [a]
-- ('^..') :: s -> 'Iso'' s a       -> [a]
-- ('^..') :: s -> 'Traversal'' s a -> [a]
-- ('^..') :: s -> 'Prism'' s a     -> [a]
-- ('^..') :: s -> 'Affine'' s a    -> [a]
-- @
(^..) :: s -> FoldLike (DList a) s a -> [a]
(^..) = flip toListOf
{-# INLINE (^..) #-}

-- | Right fold lift a 'Fold'.
-- >>> foldrOf'' folded (<>) (zero :: Int) [1..5]
-- 15
foldrOf :: FoldLike (Endo r) s a -> (a -> r -> r) -> r -> s -> r
foldrOf p f r = (`appEndo` r) . foldMapOf p (Endo . f)

-- >>> foldrOf' folded (><) (one :: Int) [1..5]
-- 120
--foldrOf' :: FoldLike (Prod (End c)) s a -> (a -> c -> c) -> c -> s -> c
--foldrOf' p f r = (`appEnd` r) . productOf p (End . f)

-- | Left fold lift a 'Fold'. 
foldlOf :: FoldLike (Dual (Endo c)) s a -> (c -> a -> c) -> c -> s -> c
foldlOf p f r = (`appEndo` r) . getDual . foldMapOf p (Dual . Endo . flip f)

-- | Fold lift the elements of a structure, associating to the left, but strictly.
--
-- @
-- 'Data.Foldable.foldl'' ≡ 'foldlOf'' 'folded'
-- @
--
-- @
-- 'foldlOf'' :: 'Iso'' s a        -> (c -> a -> c) -> c -> s -> c
-- 'foldlOf'' :: 'Lens'' s a       -> (c -> a -> c) -> c -> s -> c
-- 'foldlOf'' :: 'Getter' s a        -> (c -> a -> c) -> c -> s -> c
-- 'foldlOf'' :: 'Fold' s a        -> (c -> a -> c) -> c -> s -> c
-- 'foldlOf'' :: 'Traversal'' s a  -> (c -> a -> c) -> c -> s -> c
-- 'foldlOf'' :: 'Affine'' s a -> (c -> a -> c) -> c -> s -> c
-- @
foldlOf' :: FoldLike (Endo (Endo c)) s a -> (c -> a -> c) -> c -> s -> c
foldlOf' o f c0 s = foldrOf o f' (Endo id) s `appEndo` c0
  where f' x (Endo k) = Endo $ \z -> k $! f z x
{-# INLINE foldlOf' #-}

toEndoOf :: FoldLike (Endo (a -> a)) s (a -> a) -> s -> a -> a
toEndoOf o = foldrOf o (.) id

toEndoMOf :: Monad m => FoldLike (Endo (a -> m a)) s (a -> m a) -> s -> a -> m a
toEndoMOf o = foldrOf o (<=<) pure

allOf :: FoldLike All s a -> (a -> Bool) -> s -> Bool
allOf o p = getAll . foldMapOf o (All . p)

anyOf :: FoldLike Any s a -> (a -> Bool) -> s -> Bool
anyOf o p = getAny . foldMapOf o (Any . p)

nullOf :: FoldLike All s a -> s -> Bool
nullOf o = allOf o (const False)

-- | Whether a `Fold` contains a given element.
elemOf :: Eq a => FoldLike Any s a -> a -> s -> Bool
elemOf p a = anyOf p (== a)

-- | Whether a `Fold` not contains a given element.
notElemOf :: Eq a => FoldLike All s a -> a -> s -> Bool
notElemOf p a = allOf p (/= a)

-- | Determines whether a `Fold` has at least one focus.
--
has :: FoldLike Any s a -> s -> Bool
has p = getAny . foldMapOf p (const (Any True))

-- | Determines whether a `Fold` does not have a focus.
--
hasnt :: FoldLike All s a -> s -> Bool
hasnt p = getAll . foldMapOf p (const (All False))

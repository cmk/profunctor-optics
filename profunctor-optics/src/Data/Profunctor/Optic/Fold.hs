module Data.Profunctor.Optic.Fold where

import Data.Foldable (traverse_)
import Data.Profunctor.Optic.Type 
import Data.Profunctor.Optic.Prelude
import Data.Profunctor.Optic.Getter (view, to)


import Data.DList.NonEmpty (NonEmptyDList)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NEL
import qualified Data.DList.NonEmpty as NEL


import Data.DList (DList)
import qualified Data.DList as L

---------------------------------------------------------------------
-- 'Fold'
---------------------------------------------------------------------

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
folding f = rcoerce . lmap f . wander traverse_
{-# INLINE folding #-}

-- | Obtain a 'Fold' using a 'Traversable' functor.
--
-- @
-- 'folding'' f ≡ 'traverse'' . 'lmap' f . 'rcoerce'
-- 'folding'' f ≡ 'wander' 'traverse' . 'to' f
-- @
--
folding' :: Traversable f => (s -> a) -> Fold (f s) a
folding' f = wander traverse . to f

folded :: Foldable f => Fold (f a) a
folded = folding id

cloneFold :: Monoid a => FoldLike a s a -> Fold s a
cloneFold = to . view


---------------------------------------------------------------------
-- 'Fold1'
---------------------------------------------------------------------

{-
A 'Fold1' can interpret 'a' in a semigroup so long as 's' can also be interpreted that way.


Fold1 laws:

fold_complete :: Fold1 s a -> Bool
fold_complete o = tripping o $ folding1 (toNelOf o)
-}

{-

-- folding1 (0 :|) :: Fold1 [Int] Int
folding1 :: Foldable1 f => (s -> f a) -> Fold1 s a
folding1 f = to f . wander1 traverse1_

-- folding1' First :: Traversable1 f => Fold1 (f a) (First a)
-- folding1' Min :: Traversable1 f => Fold1 (f a) (Min a)
folding1' :: Traversable1 f => (s -> a) -> Fold1 (f s) a
folding1' f = wander1 traverse1 . to f


folded1 :: Foldable1 f => Fold1 (f a) a
folded1 = folding1 id

foldMapping :: ((a -> r) -> s -> r) -> FoldLike r s a
foldMapping = between (ustar Const) (dstar getConst) 

cloneFold1 :: Semigroup a => FoldLike a s a -> Fold1 s a
cloneFold1 = to . view
-}

---------------------------------------------------------------------
-- Primitive Operators
---------------------------------------------------------------------

-- | Map each part of a structure viewed through a 'Lens', 'Getter',
-- 'Fold' or 'Traversal' to a monoid and combine the results.
--
-- >>> foldMapOf both id (["foo"], ["bar", "baz"])
-- ["foo","bar","baz"]
--
-- @
-- 'Data.Foldable.foldMap' = 'foldMapOf' 'folded'
-- @
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
-- 'foldMapOf' :: 'Monoid' r    => 'Affine'' s a -> (a -> r) -> s -> r
-- 'foldMapOf' :: 'Semigroup' r => 'Traversal1'' s a -> (a -> r) -> s -> r
-- 'foldMapOf' :: 'Monoid' r    => 'Fold' s a        -> (a -> r) -> s -> r
-- 'foldMapOf' :: 'Semigroup' r => 'Fold1' s a       -> (a -> r) -> s -> r
-- @
--
-- @
-- 'foldMapOf' :: 'AFold' r s a -> (a -> r) -> s -> r
-- @
foldMapOf :: FoldLike r s a -> (a -> r) -> s -> r
foldMapOf = between (dstar getConst) (ustar Const)


-- | Collects the foci of a `Fold` into a list.
toListOf :: FoldLike (DList a) s a -> s -> [a]
toListOf o = flip L.apply [] . foldMapOf o L.singleton 

-- | Extract a 'NonEmpty' of the targets of 'Fold1'.
--
-- >>> toNelOf both1 ("hello", "world")
-- "hello" :| ["world"]
--
-- @
-- 'toNelOf' :: 'Getter' s a        -> s -> NonEmpty a
-- 'toNelOf' :: 'Fold1' s a       -> s -> NonEmpty a
-- 'toNelOf' :: 'Lens'' s a       -> s -> NonEmpty a
-- 'toNelOf' :: 'Iso'' s a        -> s -> NonEmpty a
-- 'toNelOf' :: 'Traversal1'' s a -> s -> NonEmpty a
-- 'toNelOf' :: 'Prism'' s a      -> s -> NonEmpty a
-- @
toNelOf :: FoldLike (NonEmptyDList a) s a -> s -> NonEmpty a
toNelOf o = flip NEL.apply [] . foldMapOf o NEL.singleton


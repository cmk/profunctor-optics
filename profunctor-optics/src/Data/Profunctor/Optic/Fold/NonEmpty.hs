module Data.Profunctor.Optic.Fold.NonEmpty where

import Data.DList.NonEmpty (NonEmptyDList)
import Data.Functor.Apply (Apply(..))
import Data.List.NonEmpty (NonEmpty(..))
import Data.Profunctor.Optic.Getter (view, to)
import Data.Profunctor.Optic.Prelude
import Data.Profunctor.Optic.Type
import Data.Semigroup
import Data.Semigroup.Foldable
import Data.Semigroup.Traversable
import qualified Data.DList.NonEmpty as NEL

---------------------------------------------------------------------
-- 'Fold1'
---------------------------------------------------------------------

type AFold1 r s a = Semigroup r => FoldLike r s a

{-
A 'Fold1' can interpret 'a' in a semigroup so long as 's' can also be interpreted that way.
Fold1 laws:
fold1_complete :: Fold1 s a -> Bool
fold1_complete o = tripping o $ folding1 (toNelOf o)
-}

-- | Obtain a 'Fold' by lifting an operation that returns a 'Foldable' result.
--
-- This can be useful to lift operations from @Data.List@ and elsewhere into a 'Fold'.
--
-- >>> [1,2,3,4] ^.. folding tail
-- [2,3,4]
--
folding1 :: Foldable1 f => (s -> f a) -> Fold1 s a
folding1 f = rcoerce . lmap f . over traverse1_
{-# INLINE folding1 #-}

folded1 :: Traversable1 f => (s -> a) -> Fold1 (f s) a
folded1 f = over traverse1 . to f

fold1Like :: Semigroup r => ((a -> r) -> s -> r) -> AFold1 r s a
fold1Like = between (ustar Const) (dstar getConst)

fold1Like' :: Foldable1 f => AFold1 r (f a) a
fold1Like' = fold1Like foldMap1

cloneFold1 :: Semigroup a => FoldLike a s a -> Fold1 s a
cloneFold1 = to . view

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

foldMap1Of :: Semigroup r => FoldLike r s a -> (a -> r) -> s -> r
foldMap1Of = between (dstar getConst) (ustar Const)

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
toNelOf o = flip NEL.apply [] . foldMap1Of o NEL.singleton

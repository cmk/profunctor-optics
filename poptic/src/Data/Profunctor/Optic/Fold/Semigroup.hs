module Data.Profunctor.Optic.Fold.Semigroup where

import Data.Semigroup
import Data.Semiring
import Data.Profunctor.Optic.Type 
import Data.Profunctor.Optic.Operator
import Data.Profunctor.Optic.Prelude

import Data.Profunctor.Optic.View (view, to)
import Data.Profunctor.Optic.Prism (_Just, filtering)
import Data.Foldable (traverse_)
--import Data.Functor.Const (Const(..))
import Control.Monad ((<=<))
import Control.Monad.Reader as Reader
import Control.Monad.State as State

import Data.DList.NonEmpty (NonEmptyDList)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NEL
import qualified Data.DList.NonEmpty as NEL

---------------------------------------------------------------------
-- 'Fold1'
---------------------------------------------------------------------


{-
Fold1 laws:

fold_complete :: Fold1 s a -> Bool
fold_complete o = tripping o $ folding1 (toNelOf o)
-}

-- folding1 (0 :|) :: Fold1 [Int] Int
folding1 :: Foldable1 f => (s -> f a) -> Fold1 s a
folding1 f = to f . wander1 traverse1_

-- folding1' First :: Traversable1 f => Fold1 (f a) (First a)
-- folding1' Min :: Traversable1 f => Fold1 (f a) (Min a)
folding1' :: Traversable1 f => (s -> a) -> Fold1 (f s) a
folding1' f = wander1 traverse1 . to f

folded1 :: Foldable1 f => Fold1 (f a) a
folded1 = folding1 id

--cloneFold1 :: Semigroup r => AFold r s a -> Fold1 s a
--cloneFold1 f = to $ \s -> getConst (f Const s)


---------------------------------------------------------------------
-- Primitive Operators
---------------------------------------------------------------------

-- | Map each part of a structure viewed through a 'Lens', 'View',
-- 'Fold' or 'Traversal' to a monoid and combine the results.
--
-- >>> foldMapOf both id (["foo"], ["bar", "baz"])
-- ["foo","bar","baz"]
--
-- @
-- 'Data.Foldable.foldMap' = 'productOf 'folded'
-- @
--
-- @
-- 'productOf ≡ 'views'
-- @
--
-- @
-- 'productOf ::                  'Iso'' s a        -> (a -> r) -> s -> r
-- 'productOf ::                  'Lens'' s a       -> (a -> r) -> s -> r
-- 'productOf :: 'Monoid' r    => 'Prism'' s a      -> (a -> r) -> s -> r
-- 'productOf :: 'Monoid' r    => 'Traversal'' s a  -> (a -> r) -> s -> r
-- 'productOf :: 'Monoid' r    => 'Traversal0'' s a -> (a -> r) -> s -> r
-- 'productOf :: 'Semigroup' r => 'Traversal1'' s a -> (a -> r) -> s -> r
-- 'productOf :: 'Monoid' r    => 'Fold' s a        -> (a -> r) -> s -> r
-- 'productOf :: 'Semigroup' r => 'Fold1' s a       -> (a -> r) -> s -> r
-- 'productOf ::                  'AFold' s a       -> (a -> r) -> s -> r
-- @
--
-- @
-- 'productOf :: 'AFold' r s a -> (a -> r) -> s -> r
-- @
foldMapOf :: AFold r s a -> (a -> r) -> s -> r
foldMapOf = between (dstar getConst) (ustar Const)

foldMapOf' :: Optic' (Forget' r) s a -> (a -> r) -> s -> r
foldMapOf' o f = g where Forget' g = o (Forget' f) 

-- | Extract a 'NonEmpty' of the targets of 'Fold1'.
--
-- >>> toNelOf both1 ("hello", "world")
-- "hello" :| ["world"]
--
-- @
-- 'toNelOf' :: 'View' s a      -> s -> NonEmpty a
-- 'toNelOf' :: 'Fold1' s a       -> s -> NonEmpty a
-- 'toNelOf' :: 'Lens'' s a       -> s -> NonEmpty a
-- 'toNelOf' :: 'Iso'' s a        -> s -> NonEmpty a
-- 'toNelOf' :: 'Traversal1'' s a -> s -> NonEmpty a
-- 'toNelOf' :: 'Prism'' s a      -> s -> NonEmpty a
-- @
toNelOf :: AFold (NonEmptyDList a) s a -> s -> NonEmpty a
toNelOf o = flip NEL.apply [] . foldMapOf o NEL.singleton


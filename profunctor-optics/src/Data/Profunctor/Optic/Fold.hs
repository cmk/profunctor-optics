module Data.Profunctor.Optic.Fold where

import Control.Monad ((<=<))
import Data.DList (DList)
import Data.Foldable (traverse_)
import Data.Functor.Foldable (Recursive, Base, fold)
import Data.Monoid
import Data.Profunctor.Optic.View (to)
import Data.Profunctor.Optic.Prelude
import Data.Profunctor.Optic.Traversal
import Data.Profunctor.Optic.Type

import qualified Data.DList as DL


import Data.Functor.Foldable (ListF(..))
import Data.Functor.Base (NonEmptyF(..))
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
--
-- See 'Data.Profunctor.Optic.Property'.
--
folding :: Foldable f => (s -> f a) -> Fold s a
folding f = coercer . lmap f . lift traverse_
{-# INLINE folding #-}

-- | Obtain a 'Fold' using a 'Traversable' functor.
--
-- @
-- 'folded' f ≡ 'lift' 'traverse' . 'to' f
-- @
--
folded :: Traversable f => (s -> a) -> Fold (f s) a
folded f = traversed . coercer . lmap f

foldLike :: Monoid r => ((a -> r) -> s -> r) -> AFold r s a
foldLike = between (Star . (Const .)) ((getConst .) . runStar)

foldLike' :: Foldable f => AFold r (f a) a
foldLike' = foldLike foldMap

{-
fromListF :: Num a => ListF a (Sum a) -> Sum a
fromListF Nil = mempty
fromListF (Cons a r) = Sum a <> r

foldMapOf (recursing) fromListF $ [1..5]
Sum {getSum = 15}
-}

recursing :: Recursive s => AFold a s (Base s a)
recursing = foldLike fold

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | Map each part of a structure viewed through a 'Lens', 'View',
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
-- 'foldMapOf' :: 'Monoid' r    => 'Traversal0'' s a     -> (a -> r) -> s -> r
-- 'foldMapOf' :: 'Monoid' r    => 'Fold' s a        -> (a -> r) -> s -> r
-- 'foldMapOf' :: 'Semigroup' r => 'Fold1' s a       -> (a -> r) -> s -> r
-- @
--
foldMapOf :: Monoid r => AFold r s a -> (a -> r) -> s -> r
foldMapOf = between ((getConst .) . runStar) (Star . (Const .))

-- | Collects the foci of a `Fold` into a list.
--
toListOf :: AFold (DList a) s a -> s -> [a]
toListOf o = flip DL.apply [] . foldMapOf o DL.singleton

-- |
--
foldOf :: Monoid a => AFold a s a -> s -> a
foldOf = flip foldMapOf id

-- @
-- toPureOf :: Fold s a -> s -> [a]
-- toPureOf :: Applicative f => Setter s t a b -> s -> f a
-- @
toPureOf :: Applicative f => Monoid (f a) => AFold (f a) s a -> s -> f a
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
-- ('^..') :: s -> 'View' s a     -> [a]
-- ('^..') :: s -> 'Fold' s a       -> [a]
-- ('^..') :: s -> 'Lens'' s a      -> [a]
-- ('^..') :: s -> 'Iso'' s a       -> [a]
-- ('^..') :: s -> 'Traversal'' s a -> [a]
-- ('^..') :: s -> 'Prism'' s a     -> [a]
-- ('^..') :: s -> 'Traversal0'' s a    -> [a]
-- @
(^..) :: s -> AFold (DList a) s a -> [a]
(^..) = flip toListOf
{-# INLINE (^..) #-}

-- | Right fold lift a 'Fold'.
-- >>> foldrOf'' folded (<>) (zero :: Int) [1..5]
-- 15
foldrOf :: AFold (Endo r) s a -> (a -> r -> r) -> r -> s -> r
foldrOf p f r = (`appEndo` r) . foldMapOf p (Endo . f)

-- | Left fold lift a 'Fold'.
--
foldlOf :: AFold (Dual (Endo c)) s a -> (c -> a -> c) -> c -> s -> c
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
-- 'foldlOf'' :: 'View' s a        -> (c -> a -> c) -> c -> s -> c
-- 'foldlOf'' :: 'Fold' s a        -> (c -> a -> c) -> c -> s -> c
-- 'foldlOf'' :: 'Traversal'' s a  -> (c -> a -> c) -> c -> s -> c
-- 'foldlOf'' :: 'Traversal0'' s a -> (c -> a -> c) -> c -> s -> c
-- @
foldlOf' :: AFold (Endo (Endo c)) s a -> (c -> a -> c) -> c -> s -> c
foldlOf' o f c0 s = foldrOf o f' (Endo id) s `appEndo` c0
  where f' x (Endo k) = Endo $ \z -> k $! f z x
{-# INLINE foldlOf' #-}

toEndoOf :: AFold (Endo (a -> a)) s (a -> a) -> s -> a -> a
toEndoOf o = foldrOf o (.) id

toEndoMOf :: Monad m => AFold (Endo (a -> m a)) s (a -> m a) -> s -> a -> m a
toEndoMOf o = foldrOf o (<=<) pure

allOf :: AFold All s a -> (a -> Bool) -> s -> Bool
allOf o p = getAll . foldMapOf o (All . p)

anyOf :: AFold Any s a -> (a -> Bool) -> s -> Bool
anyOf o p = getAny . foldMapOf o (Any . p)

nullOf :: AFold All s a -> s -> Bool
nullOf o = allOf o (const False)

-- | Whether a `Fold` contains a given element.
elemOf :: Eq a => AFold Any s a -> a -> s -> Bool
elemOf p a = anyOf p (== a)

-- | Whether a `Fold` not contains a given element.
notElemOf :: Eq a => AFold All s a -> a -> s -> Bool
notElemOf p a = allOf p (/= a)

-- | Determines whether a `Fold` has at least one focus.
--
has :: AFold Any s a -> s -> Bool
has p = getAny . foldMapOf p (const (Any True))

-- | Determines whether a `Fold` does not have a focus.
--
hasnt :: AFold All s a -> s -> Bool
hasnt p = getAll . foldMapOf p (const (All False))

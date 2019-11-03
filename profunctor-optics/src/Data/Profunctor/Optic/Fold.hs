module Data.Profunctor.Optic.Fold where

import Control.Monad ((<=<))
import Data.Foldable (Foldable, foldMap, traverse_)
import Data.Functor.Foldable (Recursive, Base, fold)
import Data.Monoid
import Data.Profunctor.Optic.View (to)
import Data.Profunctor.Optic.Prelude
import Data.Profunctor.Optic.Traversal
import Data.Profunctor.Optic.Type

import Control.Foldl (EndoM(..))
import qualified Control.Foldl as L
import qualified Data.Functor.Foldable as F

import Data.Functor.Foldable (ListF(..))
import Data.Functor.Base (NonEmptyF(..))

---------------------------------------------------------------------
-- 'Fold'
---------------------------------------------------------------------

-- | Obtain a 'Fold' using a 'Traversable' functor.
--
-- @
-- 'folding' f ≡ 'lift' 'traverse' . 'to' f
-- @
--
folding :: Traversable f => (s -> a) -> Fold (f s) a
folding f = traversed . coercer . lmap f
{-# INLINE folding #-}

-- | Obtain a 'Fold' by lifting an operation that returns a 'Foldable' result.
--
-- @ 
-- 'folding_' ('toListOf' o) ≡ o
-- @
--
-- This can be useful to lift operations from @Data.List@ and elsewhere into a 'Fold'.
--
-- >>> [1,2,3,4] ^.. folding_ tail
-- [2,3,4]
--
--
-- See 'Data.Profunctor.Optic.Property'.
--
folding_ :: Foldable f => (s -> f a) -> Fold s a
folding_ f = coercer . lmap f . lift traverse_
{-# INLINE folding_ #-}

---------------------------------------------------------------------
-- 'FoldRep'
---------------------------------------------------------------------

-- | TODO: Document
--
afold :: Monoid r => ((a -> r) -> s -> r) -> AFold r s a
afold = between (Star . (Const .)) ((getConst .) . runStar)

-- | TODO: Document
--
afold' :: Foldable f => AFold r (f a) a
afold' = afold foldMap

{-
fromListF :: Num a => ListF a (Sum a) -> Sum a
fromListF Nil = mempty
fromListF (Cons a r) = Sum a <> r

foldMapOf (recursing) fromListF $ [1..5]
Sum {getSum = 15}
-}

-- | TODO: Document
--
recursing :: Recursive s => AFold a s (Base s a)
recursing = afold F.fold

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
toListOf :: AFold (Endo [a]) s a -> s -> [a]
toListOf o = foldrOf o (:) []

-- | TODO: Document
--
foldOf :: Monoid a => AFold a s a -> s -> a
foldOf = flip foldMapOf id

-- @
-- toPureOf :: Fold s a -> s -> [a]
-- toPureOf :: Applicative f => Setter s t a b -> s -> f a
-- @
toPureOf :: Applicative f => Monoid (f a) => AFold (f a) s a -> s -> f a
toPureOf o = foldMapOf o pure

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
foldlOf' o f c s = foldrOf o f' (Endo id) s `appEndo` c
  where f' x (Endo k) = Endo $ \z -> k $! f z x
{-# INLINE foldlOf' #-}

-- | TODO: Document
--
foldMlOf' :: Monad m => AFold (Endo (EndoM m r)) s a -> (r -> a -> m r) -> r -> s -> m r
foldMlOf' o f c s = foldrOf o f' mempty s `appEndoM` c
  where f' x (EndoM k) = EndoM $ \z -> (f $! z) x >>= k

-- | TODO: Document
--
toEndoOf :: AFold (Endo (a -> a)) s (a -> a) -> s -> a -> a
toEndoOf o = foldrOf o (.) id

-- | TODO: Document
--
toEndoMOf :: Monad m => AFold (Endo (a -> m a)) s (a -> m a) -> s -> a -> m a
toEndoMOf o = foldrOf o (<=<) pure

---------------------------------------------------------------------
-- Derived operators
---------------------------------------------------------------------

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
(^..) :: s -> AFold (Endo [a]) s a -> [a]
(^..) = flip toListOf
{-# INLINE (^..) #-}

-- | TODO: Document
--
lmaps :: Handler b a -> L.Fold a c -> L.Fold b c
lmaps o (L.Fold h z k) = L.Fold (foldlOf' o h) z k

-- | TODO: Document
--
lmaps' :: Monad m => HandlerM m b a -> L.FoldM m a c -> L.FoldM m b c
lmaps' o (L.FoldM h z k) = L.FoldM (foldMlOf' o h) z k

-- | TODO: Document
--
all :: AFold All s a -> (a -> Bool) -> s -> Bool
all o p = getAll . foldMapOf o (All . p)

-- | TODO: Document
--
any :: AFold Any s a -> (a -> Bool) -> s -> Bool
any o p = getAny . foldMapOf o (Any . p)

-- | TODO: Document
--
null :: AFold All s a -> s -> Bool
null o = all o (const False)

-- | Whether a `Fold` contains a given element.
elem :: Eq a => AFold Any s a -> a -> s -> Bool
elem p a = any p (== a)

-- | Whether a `Fold` not contains a given element.
notElem :: Eq a => AFold All s a -> a -> s -> Bool
notElem p a = all p (/= a)

-- | Determines whether a `Fold` has at least one focus.
--
has :: AFold Any s a -> s -> Bool
has p = getAny . foldMapOf p (const (Any True))

-- | Determines whether a `Fold` does not have a focus.
--
hasnt :: AFold All s a -> s -> Bool
hasnt p = getAll . foldMapOf p (const (All False))

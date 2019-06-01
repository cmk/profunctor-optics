module Data.Profunctor.Optic.Fold (
    module Data.Profunctor.Optic.Fold 
  , module Export
) where

import Data.Profunctor.Optic.Fold.NonEmpty as Export
import Data.Profunctor.Optic.Fold.Affine   as Export

import Data.Semigroup
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

import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE


---------------------------------------------------------------------
-- 'Fold'
---------------------------------------------------------------------

{-
 have to pick some Foldable. List is a safe choice (DList would be more efficient).

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
folding :: Foldable f => (s -> f a) -> Fold s a
folding f = to f . wander traverse_
{-# INLINE folding #-}

--folding :: Foldable f => (s -> f a) -> Fold s a
--folding sfa agb = phantom . traverse_ agb . sfa



-- | Obtain a 'Fold' using a 'Traversable' functor.
--
-- @
-- 'folding'' f ≡ 'traverse'' . 'lmap' f . 'ocoerce'
-- 'folding'' f ≡ 'ocoerce' . 'wander' 'traverse_' . 'lmap' f
-- 'folding'' f ≡ 'wander' 'traverse' . 'to' f
-- @
--
folding' :: Traversable f => (s -> a) -> Fold (f s) a
folding' f = wander traverse . to f



{-
cloneFold :: Monoid r => Folding r s a -> Fold s a
cloneFold f = to $ \s -> getConst (f Const s)
-}



{-


-- | Folds over a `Foldable` container.
folded :: Foldable f => Monoid r => Folding r (f a) a
folded (Star Const) = undefined --Star $ Const . foldMap a

-- | Folds over a `Foldable` container.
--folded :: (Foldable f, Monoid r) => (a -> r) -> Folding r (f a) a
folded :: (Foldable f, Monoid r) => (a -> r) -> Star (Const r) (f a) a
folded f = forget (foldMap f)

cofolded :: (Foldable f, Monoid r) => (a -> r) -> Costar f a r
cofolded f = Costar (foldMap f)


-- | Replicates the elements of a fold.
replicated :: Monoid r => Int -> Folding r s a
replicated i (Star (Const a)) = Star (Const (go i a))
  where go 0 _ = mempty
        go n x = x <> go (n - 1) x

-- | Builds a `Fold` using an unfold.
unfolded :: Monoid r => (s -> Maybe (a, s)) -> Folding r s a
unfolded f p = Star (Const go)
  where
  go = maybe mempty (\(a, sn) -> runStar (Const p a <> go sn) . f)


-- | Build a 'Fold' that unfolds its values from a seed.
--
-- @
-- 'Prelude.unfoldr' ≡ 'toListOf' '.' 'unfolded'
-- @
--
-- >>> 10^..unfolded (\b -> if b == 0 then Nothing else Just (b, b-1))
-- [10,9,8,7,6,5,4,3,2,1]
unfolded :: (b -> Maybe (a, b)) -> Fold b a
unfolded f g b0 = go b0 where
  go b = case f b of
    Just (a, b') -> g a *> go b'
    Nothing      -> noEffect
{-# INLINE unfolded #-}

-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

foldOf :: Folding a s a -> s -> a
foldOf = flip foldMapOf id


-- @
-- toPureOf :: Fold s a -> s -> [a]
-- toPureOf :: (Applicative f, Monoid (f a)) => Fold s a -> s -> f a
-- toPureOf :: Applicative f => Over s t a b -> s -> f a
-- @
toPureOf :: Applicative f => Folding (f a) s a -> s -> f a
toPureOf o = foldMapOf o pure

-- | Collects the foci of a `Fold1` into a non-empty list.
--toNelOf :: Folding (Endo (NonEmpty a)) s a -> s -> NonEmpty a
--toNelOf o = undefined

-- | Collects the foci of a `Fold` into a list.
toListOf :: Folding (Endo [a]) s a -> s -> [a]
toListOf o = foldrOf o (:) []


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
-- ('^..') :: s -> 'Affine'' s a    -> [a]
-- @
(^..) :: s -> Folding (Endo [a]) s a -> [a]
(^..) = flip toListOf
{-# INLINE (^..) #-}



sumOf :: Num a => Folding (Sum a) s a -> s -> a
sumOf o = getSum . foldMapOf o Sum

productOf :: Num a => Folding (Product a) s a -> s -> a
productOf o = getProduct . foldMapOf o Product

allOf :: Folding All s a -> (a -> Bool) -> s -> Bool
allOf o p = getAll . foldMapOf o (All . p)

anyOf :: Folding Any s a -> (a -> Bool) -> s -> Bool
anyOf o p = getAny . foldMapOf o (Any . p)

lengthOf :: Num r => Folding (Sum r) s a -> s -> r
lengthOf o = getSum . foldMapOf o (const (Sum 1))

nullOf :: Folding All s a -> s -> Bool
nullOf o = allOf o (const False)

-- | Right fold over a 'Fold'.
foldrOf :: Folding (Endo c) s a -> (a -> c -> c) -> c -> s -> c
foldrOf p f r = flip appEndo r . foldMapOf p (Endo . f)

-- | Left fold over a 'Fold'.
foldlOf :: Folding (Dual (Endo c)) s a -> (c -> a -> c) -> c -> s -> c
foldlOf p f r = flip appEndo r . getDual . foldMapOf p (Dual . Endo . flip f)

-- | Traverse the foci of a `Fold`, discarding the results.
traverseOf_
  :: Applicative f 
  => Folding (Endo (f ())) s a -> (a -> f x) -> s -> f ()
traverseOf_ p f = foldrOf p (\a f' -> (() <$) (f a) *> f') $ pure ()

sequenceOf_
  :: Applicative f 
  => Folding (Endo (f ())) s (f a) -> s -> f ()
sequenceOf_ p = traverseOf_ p id

-- | Whether a `Fold` contains a given element.
elemOf :: Eq a => Folding Any s a -> a -> s -> Bool
elemOf p a = anyOf p (== a)

-- | Whether a `Fold` not contains a given element.
notElemOf :: Eq a => Folding All s a -> a -> s -> Bool
notElemOf p a = allOf p (/= a)

-- | Determines whether a `Fold` has at least one focus.
--
has :: Folding Any s a -> s -> Bool
has p = getAny . foldMapOf p (const (Any True))

-- | Determines whether a `Fold` does not have a focus.
--
hasnt :: Folding All s a -> s -> Bool
hasnt p = getAll . foldMapOf p (const (All False))

toEndoOf :: Folding (Endo (a -> a)) s (a -> a) -> s -> a -> a
toEndoOf o = foldrOf o (.) id

toEndoMOf :: Monad m => Folding (Endo (a -> m a)) s (a -> m a) -> s -> a -> m a
toEndoMOf o = foldrOf o (<=<) pure




module Data.Profunctor.Optic.Fold.Monoid where

import Data.Monoid
import Data.Profunctor.Optic.Type 
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.Prelude

import Data.Profunctor.Optic.Getter (view, to)
import Data.Profunctor.Optic.Prism (_Just, filtering)
import Data.Foldable (traverse_)
--import Data.Functor.Const (Const(..))

import Control.Monad ((<=<))
import Control.Monad.Reader as Reader
import Control.Monad.State as State

import Data.Semiring
import Data.Semiring.Endomorphism

-- A 'Fold' can interpret 'a' in a monoid so long as 's' can also be interpreted that way.

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


folded :: Foldable f => Fold (f a) a
folded = folding id


{-
cloneFold :: Monoid r => FoldLike r s a -> Fold s a
cloneFold f = to $ \s -> getConst (f Const s)
-}



{-


-- | Folds over a `Foldable` container.
folded :: Foldable f => Monoid r => FoldLike r (f a) a
folded (Star Const) = undefined --Star $ Const . foldMap a
folded (Forget a) = Forget (foldMap a)

-- | Folds over a `Foldable` container.
--folded :: (Foldable f, Monoid r) => (a -> r) -> FoldLike r (f a) a
folded :: (Foldable f, Monoid r) => (a -> r) -> Star (Const r) (f a) a
folded f = forget (foldMap f)

cofolded :: (Foldable f, Monoid r) => (a -> r) -> Costar f a r
cofolded f = Costar (foldMap f)



-- | A 'Fold' that replicates its input @n@ times.
--
-- @
-- 'replicate' n ≡ 'toListOf' ('replicated' n)
-- @
--
-- >>> 5^..replicated 20
-- [5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5]
replicated :: Int -> Fold a a
replicated n0 f a = go n0 where
  m = f a
  go 0 = noEffect
  go n = m *> go (n - 1)
{-# INLINE replicated #-}

-- | Replicates the elements of a fold.
replicated :: Monoid r => Int -> FoldLike r s a
replicated i (Star (Const a)) = Star (Const (go i a))
  where go 0 _ = mempty
        go n x = x <> go (n - 1) x

-- | Builds a `Fold` using an unfold.
unfolded :: Monoid r => (s -> Maybe (a, s)) -> FoldLike r s a
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
--(^..) :: s -> FoldLike (Endo [a]) s a -> [a]
(^..) = flip toListOf'
{-# INLINE (^..) #-}

-- | Collects the foci of a `Fold` into a list.
toListOf :: FoldLike (Endo [a]) s a -> s -> [a]
toListOf o = foldrOf o (:) []

toListOf' :: FoldLike (Prod (End [a])) s a -> s -> [a]
toListOf' o = foldrOf' o (:) []

toListOf'' o = foldrOf'' o (:) []

-- | Right fold over a 'Fold'.
foldrOf :: FoldLike (Endo c) s a -> (a -> c -> c) -> c -> s -> c
foldrOf p f r = (`appEndo` r) . foldMapOf p (Endo . f)

foldrOf'' p f r = (`appEnd` r) . foldMapOf p (End . f)

foldrOf' :: FoldLike (Prod (End c)) s a -> (a -> c -> c) -> c -> s -> c
foldrOf' p f r = (`appEnd` r) . foldMapOf' p (End . f)

-- | Left fold over a 'Fold'.
foldlOf :: FoldLike (Dual (Endo c)) s a -> (c -> a -> c) -> c -> s -> c
foldlOf p f r = (`appEndo` r) . getDual . foldMapOf p (Dual . Endo . flip f)

-- | Fold over the elements of a structure, associating to the left, but strictly.
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

-- | Traverse the foci of a `Fold`, discarding the results.
traverseOf_
  :: Applicative f 
  => FoldLike (Endo (f ())) s a -> (a -> f x) -> s -> f ()
traverseOf_ p f = foldrOf p (\a f' -> (() <$) (f a) *> f') $ pure ()

sequenceOf_
  :: Applicative f 
  => FoldLike (Endo (f ())) s (f a) -> s -> f ()
sequenceOf_ p = traverseOf_ p id

{-
-- | The sum of all foci of a `Fold`.
sumOf :: forall s t a b. Semiring a => Fold (Additive a) s t a b -> s -> a
sumOf p = unwrap <<< foldMapOf p Additive

-- | The product of all foci of a `Fold`.
productOf :: forall s t a b. Semiring a => Fold (Multiplicative a) s t a b -> s -> a
productOf p = unwrap <<< foldMapOf p Multiplicative

sumOf :: Num a => FoldLike (Sum a) s a -> s -> a
sumOf o = getSum . foldMapOf o Sum


-}




productOf :: Semiring r => FoldLike (Prod r) s a -> (a -> r) -> s -> r
productOf o f = getProd . foldMapOf o (Prod . f)

sumOf :: Num a => FoldLike (Sum a) s a -> s -> a
sumOf o = getSum . foldMapOf o Sum

productOf :: Num a => FoldLike (Product a) s a -> s -> a
productOf o = getProduct . foldMapOf o Product

allOf :: FoldLike All s a -> (a -> Bool) -> s -> Bool
allOf o p = getAll . foldMapOf o (All . p)

anyOf :: FoldLike Any s a -> (a -> Bool) -> s -> Bool
anyOf o p = getAny . foldMapOf o (Any . p)

lengthOf :: Num r => FoldLike (Sum r) s a -> s -> r
lengthOf o = getSum . foldMapOf o (const (Sum 1))

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




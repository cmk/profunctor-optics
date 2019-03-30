module Data.Profunctor.Optic.Fold where

import Data.Monoid
import Data.Profunctor.Optic.Getter
import Data.Profunctor.Optic.Types 
import Data.Profunctor.Optic.Operators

import Data.Foldable (traverse_)
import Data.Functor.Const (Const(..))


---------------------------------------------------------------------
-- Fold
---------------------------------------------------------------------

-- | Build an 'AffineFold' from an arbitrary function.
--
-- @
-- 'afolding' ('view' o) ≡ o . '_Just'
-- @
--
-- afolding :: (s -> Maybe a) -> AffineFold s a
afolding :: (s -> Maybe a) -> AffineFold s a
afolding f = cimap (\s -> maybe (Left s) Right (f s)) Left . right'

folding :: Foldable f => (s -> f a) -> Fold s a
folding f = cimap f (const ()) . wander traverse_

folding' :: Traversable f => (s -> a) -> Fold (f s) a
folding' f = traverse' . cimap f f

-- | Folds over a `Foldable` container.
folded :: Foldable f => Monoid r => Optic (Forget r) (f a) t a b
folded (Forget a) = Forget (foldMap a)

-- | Replicates the elements of a fold.
replicated :: Monoid r => Int -> Optic (Forget r) a t a b
replicated i (Forget a) = Forget (go i a)
  where go 0 _ = mempty
        go n x = x <> go (n - 1) x

-- | Builds a `Fold` using an unfold.
unfolded :: Monoid r => (s -> Maybe (a, s)) -> Optic (Forget r) s t a b
unfolded f p = Forget go
  where
  go = maybe mempty (\(a, sn) -> runForget p a <> go sn) . f

---------------------------------------------------------------------
-- Derived operators
---------------------------------------------------------------------
-- | Folds all foci of a `Fold` to one. Similar to 'view'.
foldOf :: Optic' (Forget a) s a -> s -> a
foldOf o = foldMapOf o id

-- @
-- toPureOf :: Fold s a -> s -> [a]
-- toPureOf :: (Applicative f, Monoid (f a)) => Fold s a -> s -> f a
-- toPureOf :: Applicative f => Setter s t a b -> s -> f a
-- @
toPureOf
  :: Applicative f 
  => Optic (Forget (f a)) s t a b -> s -> f a
toPureOf o = foldMapOf o pure

-- | Collects the foci of a `Fold` into a list.
--toListOf :: Fold (Endo [a]) s t a b -> s -> [a]
toListOf :: Optic (Forget (Endo [a])) s t a b -> s -> [a]
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
-- ('^..') :: s -> 'Getter' s a     -> [a]
-- ('^..') :: s -> 'Fold' s a       -> [a]
-- ('^..') :: s -> 'Lens'' s a      -> [a]
-- ('^..') :: s -> 'Iso'' s a       -> [a]
-- ('^..') :: s -> 'Traversal'' s a -> [a]
-- ('^..') :: s -> 'Prism'' s a     -> [a]
-- ('^..') :: s -> 'Affine'' s a    -> [a]
-- @
(^..) = flip toListOf
{-# INLINE (^..) #-}


infixl 8 ^?

-- | A more permissive infix variant of 'preview''.
--
-- Performs a safe 'head' of a 'Fold' or 'Traversal' or retrieve 'Just' 
-- the result from a 'Getter' or 'Lens'.
--
-- When using a 'Traversal' as a partial 'Lens', or a 'Fold' as a partial 
-- 'Getter' this can be a convenient way to extract the optional value.
--
-- Note: if you get stack overflows due to this, you may want to use 
-- 'firstOf' instead, which can deal more gracefully with heavily left-biased 
-- trees.
--
-- >>> Left 4 ^? _Left
-- Just 4
--
-- >>> Right 4 ^? _Left
-- Nothing
--
-- @
-- ('^?') ≡ 'flip' 'preview''
-- @
--
-- @
-- ('^?') :: s -> 'Getter' s a       -> 'Maybe' a
-- ('^?') :: s -> 'Fold' s a         -> 'Maybe' a
-- ('^?') :: s -> 'Lens'' s a        -> 'Maybe' a
-- ('^?') :: s -> 'Prism'' s a       -> 'Maybe' a
-- ('^?') :: s -> 'Affine'' s a      -> 'Maybe' a
-- ('^?') :: s -> 'Iso'' s a         -> 'Maybe' a
-- ('^?') :: s -> 'Traversal'' s a   -> 'Maybe' a
-- @
(^?) :: s -> Optic (Forget (First a)) s t a b -> Maybe a
(^?) = flip firstOf

-- | The first focus of a `Fold`, if there is any. Synonym for `preview`.
firstOf :: Optic (Forget (First a)) s t a b -> s -> Maybe a
firstOf l = getFirst . foldMapOf l (First . pure)

-- | The last focus of a `Fold`, if there is any.
lastOf :: Optic (Forget (Last a)) s t a b -> s -> Maybe a
lastOf p = getLast . foldMapOf p (Last . Just)

sumOf :: Optic (Forget (Sum a)) s t a b -> s -> a
sumOf l = getSum . foldMapOf l Sum

productOf :: Optic (Forget (Product a)) s t a b -> s -> a
productOf l = getProduct . foldMapOf l Product

allOf :: Optic (Forget All) s t a b -> (a -> Bool) -> s -> Bool
allOf l p = getAll . foldMapOf l (All . p)

anyOf :: Optic (Forget Any) s t a b -> (a -> Bool) -> s -> Bool
anyOf l p = getAny . foldMapOf l (Any . p)

lengthOf :: Num r => Optic (Forget (Sum r)) s t a b -> s -> r
lengthOf l = getSum . foldMapOf l (const (Sum 1))

nullOf :: Optic (Forget All) s t a b -> s -> Bool
nullOf l = allOf l (const False)

-- | Right fold over a 'Fold'.
foldrOf :: Optic (Forget (Endo c)) s t a b -> (a -> c -> c) -> c -> s -> c
foldrOf p f r = flip appEndo r . foldMapOf p (Endo . f)

-- | Left fold over a 'Fold'.
foldlOf :: Optic (Forget (Dual (Endo c))) s t a b -> (c -> a -> c) -> c -> s -> c
foldlOf p f r = flip appEndo r . getDual . foldMapOf p (Dual . Endo . flip f)

-- | Traverse the foci of a `Fold`, discarding the results.
traverseOf_
  :: Applicative f 
  => Optic (Forget (Endo (f ()))) s t a b -> (a -> f x) -> s -> f ()
traverseOf_ p f = foldrOf p (\a f' -> (() <$) (f a) *> f') $ pure ()

sequenceOf_
  :: Applicative f 
  => Optic (Forget (Endo (f ()))) s t (f x) b -> s -> f ()
sequenceOf_ p = traverseOf_ p id

-- | Whether a `Fold` contains a given element.
elemOf :: Eq a => Optic (Forget Any) s t a b -> a -> s -> Bool
elemOf p a = anyOf p (== a)

-- | Whether a `Fold` not contains a given element.
notElemOf :: Eq a => Optic (Forget All) s t a b -> a -> s -> Bool
notElemOf p a = allOf p (/= a)

-- | Find the first focus of a `Fold` that satisfies a predicate, if there is any.
--
--
-- findOf :: Optic (Forget (Endo (Maybe a))) s a -> (a -> Bool) -> s -> Maybe a
findOf :: Fold s a -> (a -> Bool) -> s -> Maybe a
findOf p f = 
  foldrOf p (\a -> maybe (if f a then Just a else Nothing) Just) Nothing


-- | Determines whether a `Fold` has at least one focus.
--
--has :: Optic (Forget Any) s t a b -> s -> Bool
has :: Fold s t -> s -> Bool
has p = getAny . foldMapOf p (const (Any True))


-- | Determines whether a `Fold` does not have a focus.
--
--hasnt :: Optic (Forget All) s t a b -> s -> Bool
hasnt :: Fold s t -> s -> Bool
hasnt p = getAll . foldMapOf p (const (All False))


-- | The maximum of all foci of a `Fold`, if there is any.
--
--maximumOf :: Ord a => Optic (Forget (Endo (Maybe a))) s t a b -> s -> Maybe a
maximumOf :: Ord a => Fold s a -> s -> Maybe a
maximumOf p = foldrOf p (\a -> Just . maybe a (max a)) Nothing where
  max a b = if a > b then a else b

-- | The minimum of all foci of a `Fold`, if there is any.
--
--minimumOf :: Ord a => Optic (Forget (Endo (Maybe a))) s t a b -> s -> Maybe a
minimumOf :: Ord a => Fold s a -> s -> Maybe a
minimumOf p = foldrOf p (\a -> Just . maybe a (min a)) Nothing where
  min a b = if a < b then a else b



module Data.Profunctor.Optic.Fold where

import Data.Monoid
import Data.Profunctor.Optic.Getter
import Data.Profunctor.Optic.Type hiding (Product) 
import Data.Profunctor.Optic.Operators

import Data.Foldable (traverse_)
--import Data.Functor.Const (Const(..))

import Control.Monad.Reader as Reader
import Control.Monad.State as State

---------------------------------------------------------------------
-- Fold
---------------------------------------------------------------------
{-
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
-}
{-
-- | Folds over a `Foldable` container.
folded :: Foldable f => Monoid r => AGetter r (f a) a
folded (Star Const) = undefined --Star $ Const . foldMap a

-- | Replicates the elements of a fold.
replicated :: Monoid r => Int -> AGetter r s a
replicated i (Star (Const a)) = Star (Const (go i a))
  where go 0 _ = mempty
        go n x = x <> go (n - 1) x

-- | Builds a `Fold` using an unfold.
unfolded :: Monoid r => (s -> Maybe (a, s)) -> AGetter r s a
unfolded f p = Star (Const go)
  where
  go = maybe mempty (\(a, sn) -> runStar (Const p a <> go sn) . f)
-}
---------------------------------------------------------------------
-- Derived operators
---------------------------------------------------------------------

-- @
-- toPureOf :: Fold s a -> s -> [a]
-- toPureOf :: (Applicative f, Monoid (f a)) => Fold s a -> s -> f a
-- toPureOf :: Applicative f => Setter s t a b -> s -> f a
-- @
toPureOf
  :: Applicative f 
  => AGetter (f a) s a -> s -> f a
toPureOf o = foldMapOf o pure

-- | Collects the foci of a `Fold` into a list.
--toListOf :: Fold (Endo [a]) s t a b -> s -> [a]
toListOf :: AGetter (Endo [a]) s a -> s -> [a]
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
(^..) :: s -> AGetter (Endo [a]) s a -> [a]
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
(^?) :: s -> AGetter (First a) s a -> Maybe a
(^?) = flip firstOf

-- | The first focus of a `Fold`, if there is any. Synonym for `preview`.
firstOf :: AGetter (First a) s a -> s -> Maybe a
firstOf l = getFirst . foldMapOf l (First . pure)

preview 
  :: MonadReader s m 
  => AGetter (First a) s a --Optic (Star (Pre a)) s t a b 
  -> m (Maybe a)
preview o = Reader.asks $ firstOf o

preuse 
  :: MonadState s m 
  => AGetter (First a) s a --Optic (Star (Pre a)) s t a b  
  -> m (Maybe a)
preuse o = State.gets (preview o)

-- | The last focus of a `Fold`, if there is any.
lastOf :: AGetter (Last a) s a -> s -> Maybe a
lastOf p = getLast . foldMapOf p (Last . Just)

sumOf :: AGetter (Sum a) s a -> s -> a
sumOf l = getSum . foldMapOf l Sum

productOf :: AGetter (Product a) s a -> s -> a
productOf l = getProduct . foldMapOf l Product

allOf :: AGetter All s a -> (a -> Bool) -> s -> Bool
allOf l p = getAll . foldMapOf l (All . p)

anyOf :: AGetter Any s a -> (a -> Bool) -> s -> Bool
anyOf l p = getAny . foldMapOf l (Any . p)

lengthOf :: Num r => AGetter (Sum r) s a -> s -> r
lengthOf l = getSum . foldMapOf l (const (Sum 1))

nullOf :: AGetter All s a -> s -> Bool
nullOf l = allOf l (const False)

-- | Right fold over a 'Fold'.
foldrOf :: AGetter (Endo c) s a -> (a -> c -> c) -> c -> s -> c
foldrOf p f r = flip appEndo r . foldMapOf p (Endo . f)

-- | Left fold over a 'Fold'.
foldlOf :: AGetter (Dual (Endo c)) s a -> (c -> a -> c) -> c -> s -> c
foldlOf p f r = flip appEndo r . getDual . foldMapOf p (Dual . Endo . flip f)

-- | Traverse the foci of a `Fold`, discarding the results.
traverseOf_
  :: Applicative f 
  => AGetter (Endo (f ())) s a -> (a -> f x) -> s -> f ()
traverseOf_ p f = foldrOf p (\a f' -> (() <$) (f a) *> f') $ pure ()

sequenceOf_
  :: Applicative f 
  => AGetter (Endo (f ())) s (f a) -> s -> f ()
sequenceOf_ p = traverseOf_ p id

-- | Whether a `Fold` contains a given element.
elemOf :: Eq a => AGetter Any s a -> a -> s -> Bool
elemOf p a = anyOf p (== a)

-- | Whether a `Fold` not contains a given element.
notElemOf :: Eq a => AGetter All s a -> a -> s -> Bool
notElemOf p a = allOf p (/= a)

-- | Find the first focus of a `Fold` that satisfies a predicate, if there is any.
--
findOf :: AGetter (Endo (Maybe a)) s a -> (a -> Bool) -> s -> Maybe a
findOf p f = 
  foldrOf p (\a -> maybe (if f a then Just a else Nothing) Just) Nothing


-- | Determines whether a `Fold` has at least one focus.
--
has :: AGetter Any s a -> s -> Bool
has p = getAny . foldMapOf p (const (Any True))


-- | Determines whether a `Fold` does not have a focus.
--
hasnt :: AGetter All s a -> s -> Bool
hasnt p = getAll . foldMapOf p (const (All False))


-- | The maximum of all foci of a `Fold`, if there is any.
--
maximumOf :: Ord a => AGetter (Endo (Maybe a)) s a -> s -> Maybe a
maximumOf p = foldrOf p (\a -> Just . maybe a (max a)) Nothing

-- | The minimum of all foci of a `Fold`, if there is any.
--
minimumOf :: Ord a => AGetter (Endo (Maybe a)) s a -> s -> Maybe a
minimumOf p = foldrOf p (\a -> Just . maybe a (min a)) Nothing


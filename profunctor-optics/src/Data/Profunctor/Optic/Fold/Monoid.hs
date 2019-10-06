module Data.Profunctor.Optic.Fold.Monoid where

import Data.Monoid
import Data.Profunctor.Optic.Type 
import Data.Profunctor.Optic.Prelude

import Data.Profunctor.Optic.Fold
--import Data.Profunctor.Optic.Fold.Semigroup (foldMapping, foldMapOf)
import Data.Profunctor.Optic.Prism (_Just, filtering)
import Data.Foldable (traverse_)
--import Data.Functor.Const (Const(..))

import Data.DList (DList)
import qualified Data.DList as L

import Control.Monad ((<=<))
--import Control.Monad.Reader as Reader
--import Control.Monad.State as State





---------------------------------------------------------------------
-- Primitive Operators
---------------------------------------------------------------------


--toListOf' :: FoldLike (Prod (End [a])) s a -> s -> [a]
--toListOf' o = foldrOf' o (:) []


---------------------------------------------------------------------
-- Derived Operators
---------------------------------------------------------------------


sumOf = foldMapOf

-- | Map each part of a structure viewed through a 'Lens', 'Getter',
-- 'Fold' or 'Traversal' to a product monoid and combine the results.
--
-- >>> productOf both id (["foo"], ["bar", "baz"])
-- ["foobar","foobaz"]
--
-- @
-- 'productOf' ::                  'Iso'' s a        -> (a -> r) -> s -> r
-- 'productOf' ::                  'Lens'' s a       -> (a -> r) -> s -> r
-- 'productOf' :: 'Monoid' r    => 'Prism'' s a      -> (a -> r) -> s -> r
-- 'productOf' :: 'Monoid' r    => 'Traversal'' s a  -> (a -> r) -> s -> r
-- 'productOf' :: 'Monoid' r    => 'Affine'' s a -> (a -> r) -> s -> r
-- 'productOf' :: 'Semigroup' r => 'Traversal1'' s a -> (a -> r) -> s -> r
-- 'productOf' :: 'Monoid' r    => 'Fold' s a        -> (a -> r) -> s -> r
-- 'productOf' :: 'Semigroup' r => 'Fold1' s a       -> (a -> r) -> s -> r
-- 'productOf' ::                  'AFold' s a       -> (a -> r) -> s -> r
-- @
--
-- @
-- 'Data.Semiring.foldMap'' = 'productOf' 'folded'
-- @
--
--productOf :: FoldLike (Prod r) s a -> (a -> r) -> s -> r
--productOf o f = getProd . foldMapOf o (Prod . f)

{-
-- | Calculate the 'Product' of every number targeted by a 'Fold'.
--
-- >>> productOf both (4,5)
-- 20
-- >>> productOf folded [1,2,3,4,5]
-- 120
--
-- @
-- 'Data.Foldable.product' ≡ 'productOf' 'folded'
-- @
--
-- This operation may be more strict than you would expect. If you
-- want a lazier version use @'ala' 'Product' '.' 'foldMapOf'@
--
-- @
-- 'productOf' :: 'Num' a => 'Getter' s a     -> s -> a
-- 'productOf' :: 'Num' a => 'Fold' s a       -> s -> a
-- 'productOf' :: 'Num' a => 'Lens'' s a      -> s -> a
-- 'productOf' :: 'Num' a => 'Iso'' s a       -> s -> a
-- 'productOf' :: 'Num' a => 'Traversal'' s a -> s -> a
-- 'productOf' :: 'Num' a => 'Prism'' s a     -> s -> a
-- @
productOf :: Num a => Getting (Endo (Endo a)) s a -> s -> a
productOf l = foldlOf' l (*) 1
{-# INLINE productOf #-}

-- | Calculate the 'Sum' of every number targeted by a 'Fold'.
--
-- >>> sumOf both (5,6)
-- 11
-- >>> sumOf folded [1,2,3,4]
-- 10
-- >>> sumOf (folded.both) [(1,2),(3,4)]
-- 10
-- >>> import Data.Data.Lens
-- >>> sumOf biplate [(1::Int,[]),(2,[(3::Int,4::Int)])] :: Int
-- 10
--
-- @
-- 'Data.Foldable.sum' ≡ 'sumOf' 'folded'
-- @
--
-- This operation may be more strict than you would expect. If you
-- want a lazier version use @'ala' 'Sum' '.' 'foldMapOf'@
--
-- @
-- 'sumOf' '_1' :: 'Num' a => (a, b) -> a
-- 'sumOf' ('folded' '.' 'Control.Lens.Tuple._1') :: ('Foldable' f, 'Num' a) => f (a, b) -> a
-- @
--
-- @
-- 'sumOf' :: 'Num' a => 'Getter' s a     -> s -> a
-- 'sumOf' :: 'Num' a => 'Fold' s a       -> s -> a
-- 'sumOf' :: 'Num' a => 'Lens'' s a      -> s -> a
-- 'sumOf' :: 'Num' a => 'Iso'' s a       -> s -> a
-- 'sumOf' :: 'Num' a => 'Traversal'' s a -> s -> a
-- 'sumOf' :: 'Num' a => 'Prism'' s a     -> s -> a
-- @
sumOf :: Num a => Getting (Endo (Endo a)) s a -> s -> a
sumOf l = foldlOf' l (+) 0
{-# INLINE sumOf #-}
-}

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



--foldrOf' :: FoldLike (Prod (End c)) s a -> (a -> c -> c) -> c -> s -> c
--foldrOf' p f r = (`appEnd` r) . productOf p (End . f)


-- | Right fold over a 'Fold'.
-- >>> foldrOf'' folded (<>) (zero :: Int) [1..5]
-- 15
foldrOf :: FoldLike (Endo r) s a -> (a -> r -> r) -> r -> s -> r
foldrOf p f r = (`appEndo` r) . foldMapOf p (Endo . f)


-- >>> foldrOf' folded (><) (one :: Int) [1..5]
-- 120
--foldrOf' :: FoldLike (Prod (End c)) s a -> (a -> c -> c) -> c -> s -> c
--foldrOf' p f r = (`appEnd` r) . productOf p (End . f)

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

{-

-- | Obtain the maximum element (if any) targeted by a 'Fold', 'Traversal', 'Lens', 'Iso',
-- or 'Getter' according to a user supplied 'Ordering'.
--
-- >>> maximumByOf traverse' (compare `on` length) ["mustard","relish","ham"]
-- Just "mustard"
--
-- In the interest of efficiency, This operation has semantics more strict than strictly necessary.
--
-- @
-- 'Data.Foldable.maximumBy' cmp ≡ 'Data.Maybe.fromMaybe' ('error' \"empty\") '.' 'maximumByOf' 'folded' cmp
-- @
--
-- @
-- 'maximumByOf' :: 'Getter' s a       -> (a -> a -> 'Ordering') -> s -> 'Maybe' a
-- 'maximumByOf' :: 'Fold' s a       -> (a -> a -> 'Ordering') -> s -> 'Maybe' a
-- 'maximumByOf' :: 'Iso'' s a       -> (a -> a -> 'Ordering') -> s -> 'Maybe' a
-- 'maximumByOf' :: 'Lens'' s a      -> (a -> a -> 'Ordering') -> s -> 'Maybe' a
-- 'maximumByOf' :: 'Traversal'' s a -> (a -> a -> 'Ordering') -> s -> 'Maybe' a
-- @
maximumByOf :: FoldLike (Endo (Endo (Maybe a))) s a -> (a -> a -> Ordering) -> s -> Maybe a
maximumByOf o cmp = foldlOf' o mf Nothing where
  mf Nothing y = Just $! y
  mf (Just x) y = Just $! if cmp x y == GT then x else y
{-# INLINE maximumByOf #-}



toEndoOf :: FoldLike (Endo (a -> a)) s (a -> a) -> s -> a -> a
toEndoOf o = foldrOf o (.) (Endo id)

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
-}

--lengthOf :: (Monoid r, Semiring r) => FoldLike r s a -> s -> r
--lengthOf o = foldMapOf o (const one)

-- | Calculate the number of targets there are for a 'Fold' in a given container.
--
-- /Note:/ This can be rather inefficient for large containers and just like 'length',
-- this will not terminate for infinite folds.
--
-- @
-- 'length' ≡ 'lengthOf' 'folded'
-- @
--
-- >>> lengthOf _1 ("hello",())
-- 1
--
-- >>> lengthOf traverse [1..10]
-- 10
--
-- >>> lengthOf (traverse.traverse) [[1,2],[3,4],[5,6]]
-- 6
--
-- @
-- 'lengthOf' ('folded' '.' 'folded') :: ('Foldable' f, 'Foldable' g) => f (g a) -> 'Int'
-- @
--
-- @
-- 'lengthOf' :: 'Getter' s a       -> s -> 'Int'
-- 'lengthOf' :: 'Fold' s a       -> s -> 'Int'
-- 'lengthOf' :: 'Lens'' s a      -> s -> 'Int'
-- 'lengthOf' :: 'Iso'' s a       -> s -> 'Int'
-- 'lengthOf' :: 'Traversal'' s a -> s -> 'Int'
-- @
--lengthOf :: (Monoid r, Semiring r) => FoldLike (Endo (Endo r)) s a -> s -> r
--lengthOf l = foldlOf' l (\a _ -> a <> one) zero
--{-# INLINE lengthOf #-}


{-

allOf :: FoldLike (Prod Bool) s a -> (a -> Bool) -> s -> Bool
allOf o f = productOf o f

anyOf :: FoldLike Bool s a -> (a -> Bool) -> s -> Bool
anyOf = sumOf


lengthOf :: (Monoid r, Semiring r) => FoldLike r s a -> s -> r
lengthOf o = foldMapOf o (const one)

nullOf :: FoldLike (Prod Bool) s a -> s -> Bool
nullOf o = allOf o (const False)

-- | Whether a `Fold` contains a given element.
elemOf :: Eq a => FoldLike Bool s a -> a -> s -> Bool
elemOf p a = anyOf p (== a)

-- | Whether a `Fold` not contains a given element.
notElemOf :: Eq a => FoldLike (Prod Bool) s a -> a -> s -> Bool
notElemOf p a = allOf p (/= a)

-- | Determines whether a `Fold` has at least one focus.
--
has :: FoldLike Bool s a -> s -> Bool
has p = foldMapOf p (const True)

-- | Determines whether a `Fold` does not have a focus.
--
hasnt :: FoldLike (Prod Bool) s a -> s -> Bool
hasnt p = productOf p (const False)

-}


module Data.Profunctor.Optic.Fold where

import Data.Semigroup
import Data.Profunctor.Optic.Type 
import Data.Profunctor.Optic.Operator
import Data.Profunctor.Optic.Prelude

import Data.Profunctor.Optic.Getter (view, to)
import Data.Profunctor.Optic.Prism (_Just, filtering)
import Data.Foldable (traverse_)
--import Data.Functor.Const (Const(..))

import Control.Monad ((<=<))
import Control.Monad.Reader as Reader
import Control.Monad.State as State


---------------------------------------------------------------------
-- 'AffineFold'
---------------------------------------------------------------------

-- | Build an 'AffineFold' from an arbitrary function.
--
-- @
-- 'afolding' ('view' o) ≡ o . '_Just'
-- @
--
-- afolding :: (s -> Maybe a) -> AffineFold s a
afolding :: (s -> Maybe a) -> AffineFold s a
--afolding f = cimap (\s -> maybe (Left s) Right (f s)) Left . right'
--_Just = prism Just $ maybe (Left Nothing) Right
--_Just = lmap (maybe (Left Nothing) Right) . rmap (id ||| Just) . right'

afolding f = ocoerce . lmap (\s -> maybe (Left s) Right (f s)) . right' 

-- We can freely convert between AffineFold s a and Getter s (Maybe a):
getterToAF :: Getter s (Maybe a) -> AffineFold s a
getterToAF o = afolding (view o)

-- | Build an 'AffineFold' from a 'Getter'.
--
-- @
-- 'toAffineFold' o ≡ o . '_Just'
-- 'toAffineFold' o ≡ 'afolding' ('view' o)
-- @
toAffineFold :: Getter s (Maybe a) -> AffineFold s a
toAffineFold = (. _Just)

fromAffineFold :: AffineFold s a -> Getter s (Maybe a)
fromAffineFold = to . preview

cloneAffineFold :: Getting (Maybe a) s (Maybe a) -> AffineFold s a
cloneAffineFold = (. _Just) . to . view 


---------------------------------------------------------------------
-- 'Fold' & 'Fold1'
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

-- | Build an 'AffineFold' from an arbitrary function.
--
-- @
-- 'folding'' f ≡ 'traverse'' . 'lmap' f . 'ocoerce'
-- 'folding'' f ≡ 'ocoerce' . 'wander' 'traverse_' . 'lmap' f
-- @
--

folding' :: Traversable f => (s -> a) -> Fold (f s) a
folding' f = wander traverse . to f

folding1 :: Foldable1 f => (s -> f a) -> Fold1 s a
folding1 f = to f . wander1 traverse1_






{-
cloneFold1 :: Semigroup r => Getting r s a -> Fold1 s a
cloneFold1 f = to $ \s -> getConst (f Const s)

cloneFold :: Monoid r => Getting r s a -> Fold s a
cloneFold f = to $ \s -> getConst (f Const s)

cloneAffineFold :: Semigroup r => Getting (Maybe r) s a -> Fold s a
cloneAffineFold f = to $ \s -> getConst (f Const s)
-}


{-


-- | Folds over a `Foldable` container.
folded :: Foldable f => Monoid r => Getting r (f a) a
folded (Star Const) = undefined --Star $ Const . foldMap a

-- | Folds over a `Foldable` container.
--folded :: (Foldable f, Monoid r) => (a -> r) -> Getting r (f a) a
folded :: (Foldable f, Monoid r) => (a -> r) -> Star (Const r) (f a) a
folded f = forget (foldMap f)

cofolded :: (Foldable f, Monoid r) => (a -> r) -> Costar f a r
cofolded f = Costar (foldMap f)


-- | Replicates the elements of a fold.
replicated :: Monoid r => Int -> Getting r s a
replicated i (Star (Const a)) = Star (Const (go i a))
  where go 0 _ = mempty
        go n x = x <> go (n - 1) x

-- | Builds a `Fold` using an unfold.
unfolded :: Monoid r => (s -> Maybe (a, s)) -> Getting r s a
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

-- @
-- preview :: 'Getting' ('First' a) s a -> s -> 'Maybe' a
-- @
--
preview 
  :: MonadReader s m 
  => Getting (Maybe (First a)) s a  
  -> m (Maybe a)
preview o = Reader.asks $ firstOf o

preuse 
  :: MonadState s m
  => Getting (Maybe (First a)) s a  
  -> m (Maybe a)
preuse o = State.gets (preview o)

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
(^?) :: s -> Getting (Maybe (First a)) s a -> Maybe a
(^?) = flip firstOf

-- | The first focus of a `Fold`, if there is any. Synonym for `preview`.
firstOf :: Getting (Maybe (First a)) s a -> s -> Maybe a
firstOf o s = getFirst <$> previewOf o First s

-- | The last focus of a `Fold`, if there is any.
lastOf :: Getting (Maybe (Last a)) s a -> s -> Maybe a
lastOf o s = getLast <$> previewOf o Last s


-- | Retrieve the 'Data.Semigroup.First' entry of a 'Fold1' or 'Traversal1' or the result from a 'Getter' or 'Lens'.
--
-- >>> first1Of traverse1 (1 :| [2..10])
-- 1
--
-- >>> first1Of both1 (1,2)
-- 1
--
-- /Note:/ this is different from '^.'.
--
-- >>> first1Of traverse1 ([1,2] :| [[3,4],[5,6]])
-- [1,2]
--
-- >>> ([1,2] :| [[3,4],[5,6]]) ^. traverse1
-- [1,2,3,4,5,6]
--
-- @
-- 'first1Of' :: 'Getter' s a      -> s -> a
-- 'first1Of' :: 'Fold1' s a       -> s -> a
-- 'first1Of' :: 'Lens'' s a       -> s -> a
-- 'first1Of' :: 'Iso'' s a        -> s -> a
-- 'first1Of' :: 'Traversal1'' s a -> s -> a
-- @
--
first1Of :: Getting (First a) s a -> s -> a
first1Of o = getFirst . foldMapOf o First


--afolding :: (s -> Maybe a) -> AffineFold s a
--afolding f = cimap (\s -> maybe (Left s) Right (f s)) Left . right'
--_Just = prism Just $ maybe (Left Nothing) Right
--_Just = lmap (maybe (Left Nothing) Right) . rmap (id ||| Just) . right'

--afolding f = ocoerce . lmap (\s -> maybe (Left s) Right (f s)) . right' 

findOf' :: Getting (Maybe (First a)) s a -> (a -> Bool) -> s -> Maybe a
findOf' o f = firstOf (o . filtering f)


-- | Find the innermost focus of a `Fold` that satisfies a predicate, if there is any.
--
findOf :: Getting (Endo (Maybe a)) s a -> (a -> Bool) -> s -> Maybe a
findOf o f =
  foldrOf o (\a -> maybe (if f a then Just a else Nothing) Just) Nothing


-- | The maximum of all foci of a `Fold`, if there is any.
--
maximumOf :: Ord a => Getting (Endo (Maybe a)) s a -> s -> Maybe a
maximumOf o = foldrOf o (\a -> Just . maybe a (max a)) Nothing

-- | The minimum of all foci of a `Fold`, if there is any.
--
minimumOf :: Ord a => Getting (Endo (Maybe a)) s a -> s -> Maybe a
minimumOf o = foldrOf o (\a -> Just . maybe a (min a)) Nothing

{-
-- | Obtain the maximum element (if any) targeted by a 'Fold', 'Traversal', 'Lens', 'Iso',
-- or 'Getter' according to a user supplied 'Ordering'.
--
-- >>> maximumByOf traverse (compare `on` length) ["mustard","relish","ham"]
-- Just "mustard"
--
-- In the interest of efficiency, This operation has semantics more strict than strictly necessary.
--
-- @
-- 'Data.Foldable.maximumBy' cmp ≡ 'Data.Maybe.fromMaybe' ('error' \"empty\") '.' 'maximumByOf' 'folded' cmp
-- @
--
-- @
-- 'maximumByOf' :: 'Getter' s a     -> (a -> a -> 'Ordering') -> s -> 'Maybe' a
-- 'maximumByOf' :: 'Fold' s a       -> (a -> a -> 'Ordering') -> s -> 'Maybe' a
-- 'maximumByOf' :: 'Iso'' s a       -> (a -> a -> 'Ordering') -> s -> 'Maybe' a
-- 'maximumByOf' :: 'Lens'' s a      -> (a -> a -> 'Ordering') -> s -> 'Maybe' a
-- 'maximumByOf' :: 'Traversal'' s a -> (a -> a -> 'Ordering') -> s -> 'Maybe' a
-- @
maximumByOf :: Getting (Endo (Endo (Maybe a))) s a -> (a -> a -> Ordering) -> s -> Maybe a
maximumByOf o cmp = foldlOf' o mf Nothing where
  mf Nothing y = Just $! y
  mf (Just x) y = Just $! if cmp x y == GT then x else y
{-# INLINE maximumByOf #-}

-- | Obtain the minimum element (if any) targeted by a 'Fold', 'Traversal', 'Lens', 'Iso'
-- or 'Getter' according to a user supplied 'Ordering'.
--
-- In the interest of efficiency, This operation has semantics more strict than strictly necessary.
--
-- >>> minimumByOf traverse (compare `on` length) ["mustard","relish","ham"]
-- Just "ham"
--
-- @
-- 'minimumBy' cmp ≡ 'Data.Maybe.fromMaybe' ('error' \"empty\") '.' 'minimumByOf' 'folded' cmp
-- @
--
-- @
-- 'minimumByOf' :: 'Getter' s a     -> (a -> a -> 'Ordering') -> s -> 'Maybe' a
-- 'minimumByOf' :: 'Fold' s a       -> (a -> a -> 'Ordering') -> s -> 'Maybe' a
-- 'minimumByOf' :: 'Iso'' s a       -> (a -> a -> 'Ordering') -> s -> 'Maybe' a
-- 'minimumByOf' :: 'Lens'' s a      -> (a -> a -> 'Ordering') -> s -> 'Maybe' a
-- 'minimumByOf' :: 'Traversal'' s a -> (a -> a -> 'Ordering') -> s -> 'Maybe' a
-- @
minimumByOf :: Getting (Endo (Endo (Maybe a))) s a -> (a -> a -> Ordering) -> s -> Maybe a
minimumByOf o cmp = foldlOf' o mf Nothing where
  mf Nothing y = Just $! y
  mf (Just x) y = Just $! if cmp x y == GT then y else x
{-# INLINE minimumByOf #-}

-- | The 'findOf' function takes a 'Lens' (or 'Getter', 'Iso', 'Fold', or 'Traversal'),
-- a predicate and a structure and returns the leftmost element of the structure
-- matching the predicate, or 'Nothing' if there is no such element.
--
-- >>> findOf each even (1,3,4,6)
-- Just 4
--
-- >>> findOf folded even [1,3,5,7]
-- Nothing
--
-- @
-- 'findOf' :: 'Getter' s a     -> (a -> 'Bool') -> s -> 'Maybe' a
-- 'findOf' :: 'Fold' s a       -> (a -> 'Bool') -> s -> 'Maybe' a
-- 'findOf' :: 'Iso'' s a       -> (a -> 'Bool') -> s -> 'Maybe' a
-- 'findOf' :: 'Lens'' s a      -> (a -> 'Bool') -> s -> 'Maybe' a
-- 'findOf' :: 'Traversal'' s a -> (a -> 'Bool') -> s -> 'Maybe' a
-- @
--
-- @
-- 'Data.Foldable.find' ≡ 'findOf' 'folded'
-- 'ifindOf' o ≡ 'findOf' o '.' 'Indexed'
-- @
--
-- A simpler version that didn't permit indexing, would be:
--
-- @
-- 'findOf' :: 'Getting' ('Endo' ('Maybe' a)) s a -> (a -> 'Bool') -> s -> 'Maybe' a
-- 'findOf' o p = 'foldrOf' o (\a y -> if p a then 'Just' a else y) 'Nothing'
-- @
findOf :: Getting (Endo (Maybe a)) s a -> (a -> Bool) -> s -> Maybe a
findOf o f = foldrOf o (\a y -> if f a then Just a else y) Nothing
{-# INLINE findOf #-}

-- | The 'findMOf' function takes a 'Lens' (or 'Getter', 'Iso', 'Fold', or 'Traversal'),
-- a monadic predicate and a structure and returns in the monad the leftmost element of the structure
-- matching the predicate, or 'Nothing' if there is no such element.
--
-- >>>  findMOf each ( \x -> print ("Checking " ++ show x) >> return (even x)) (1,3,4,6)
-- "Checking 1"
-- "Checking 3"
-- "Checking 4"
-- Just 4
--
-- >>>  findMOf each ( \x -> print ("Checking " ++ show x) >> return (even x)) (1,3,5,7)
-- "Checking 1"
-- "Checking 3"
-- "Checking 5"
-- "Checking 7"
-- Nothing
--
-- @
-- 'findMOf' :: ('Monad' m, 'Getter' s a)     -> (a -> m 'Bool') -> s -> m ('Maybe' a)
-- 'findMOf' :: ('Monad' m, 'Fold' s a)       -> (a -> m 'Bool') -> s -> m ('Maybe' a)
-- 'findMOf' :: ('Monad' m, 'Iso'' s a)       -> (a -> m 'Bool') -> s -> m ('Maybe' a)
-- 'findMOf' :: ('Monad' m, 'Lens'' s a)      -> (a -> m 'Bool') -> s -> m ('Maybe' a)
-- 'findMOf' :: ('Monad' m, 'Traversal'' s a) -> (a -> m 'Bool') -> s -> m ('Maybe' a)
-- @
--
-- @
-- 'findMOf' 'folded' :: (Monad m, Foldable f) => (a -> m Bool) -> f a -> m (Maybe a)
-- 'ifindMOf' o ≡ 'findMOf' o '.' 'Indexed'
-- @
--
-- A simpler version that didn't permit indexing, would be:
--
-- @
-- 'findMOf' :: Monad m => 'Getting' ('Endo' (m ('Maybe' a))) s a -> (a -> m 'Bool') -> s -> m ('Maybe' a)
-- 'findMOf' o p = 'foldrOf' o (\a y -> p a >>= \x -> if x then return ('Just' a) else y) $ return 'Nothing'
-- @
findMOf :: Monad m => Getting (Endo (m (Maybe a))) s a -> (a -> m Bool) -> s -> m (Maybe a)
findMOf o f = foldrOf o (\a y -> f a >>= \r -> if r then return (Just a) else y) $ return Nothing
{-# INLINE findMOf #-}

-- | The 'lookupOf' function takes a 'Fold' (or 'Getter', 'Traversal',
-- 'Lens', 'Iso', etc.), a key, and a structure containing key/value pairs.
-- It returns the first value corresponding to the given key. This function
-- generalizes 'lookup' to work on an arbitrary 'Fold' instead of lists.
--
-- >>> lookupOf folded 4 [(2, 'a'), (4, 'b'), (4, 'c')]
-- Just 'b'
--
-- >>> lookupOf each 2 [(2, 'a'), (4, 'b'), (4, 'c')]
-- Just 'a'
--
-- @
-- 'lookupOf' :: 'Eq' k => 'Fold' s (k,v) -> k -> s -> 'Maybe' v
-- @
lookupOf :: Eq k => Getting (Endo (Maybe v)) s (k,v) -> k -> s -> Maybe v
lookupOf o k = foldrOf o (\(k',v) next -> if k == k' then Just v else next) Nothing
{-# INLINE lookupOf #-}
-}

---------------------------------------------------------------------
-- Derived 'Fold' & 'Fold1' operators
---------------------------------------------------------------------

-- @
-- toPureOf :: Fold s a -> s -> [a]
-- toPureOf :: (Applicative f, Monoid (f a)) => Fold s a -> s -> f a
-- toPureOf :: Applicative f => Setter s t a b -> s -> f a
-- @
toPureOf
  :: Applicative f 
  => Getting (f a) s a -> s -> f a
toPureOf o = foldMapOf o pure

-- | Collects the foci of a `Fold` into a list.
--toListOf :: Fold (Endo [a]) s t a b -> s -> [a]
toListOf :: Getting (Endo [a]) s a -> s -> [a]
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
(^..) :: s -> Getting (Endo [a]) s a -> [a]
(^..) = flip toListOf
{-# INLINE (^..) #-}

sumOf :: Num a => Getting (Sum a) s a -> s -> a
sumOf o = getSum . foldMapOf o Sum

productOf :: Num a => Getting (Product a) s a -> s -> a
productOf o = getProduct . foldMapOf o Product

allOf :: Getting All s a -> (a -> Bool) -> s -> Bool
allOf o p = getAll . foldMapOf o (All . p)

anyOf :: Getting Any s a -> (a -> Bool) -> s -> Bool
anyOf o p = getAny . foldMapOf o (Any . p)

lengthOf :: Num r => Getting (Sum r) s a -> s -> r
lengthOf o = getSum . foldMapOf o (const (Sum 1))

nullOf :: Getting All s a -> s -> Bool
nullOf o = allOf o (const False)

-- | Right fold over a 'Fold'.
foldrOf :: Getting (Endo c) s a -> (a -> c -> c) -> c -> s -> c
foldrOf p f r = flip appEndo r . foldMapOf p (Endo . f)

-- | Left fold over a 'Fold'.
foldlOf :: Getting (Dual (Endo c)) s a -> (c -> a -> c) -> c -> s -> c
foldlOf p f r = flip appEndo r . getDual . foldMapOf p (Dual . Endo . flip f)

-- | Traverse the foci of a `Fold`, discarding the results.
traverseOf_
  :: Applicative f 
  => Getting (Endo (f ())) s a -> (a -> f x) -> s -> f ()
traverseOf_ p f = foldrOf p (\a f' -> (() <$) (f a) *> f') $ pure ()

sequenceOf_
  :: Applicative f 
  => Getting (Endo (f ())) s (f a) -> s -> f ()
sequenceOf_ p = traverseOf_ p id

-- | Whether a `Fold` contains a given element.
elemOf :: Eq a => Getting Any s a -> a -> s -> Bool
elemOf p a = anyOf p (== a)

-- | Whether a `Fold` not contains a given element.
notElemOf :: Eq a => Getting All s a -> a -> s -> Bool
notElemOf p a = allOf p (/= a)

-- | Determines whether a `Fold` has at least one focus.
--
has :: Getting Any s a -> s -> Bool
has p = getAny . foldMapOf p (const (Any True))

-- | Determines whether a `Fold` does not have a focus.
--
hasnt :: Getting All s a -> s -> Bool
hasnt p = getAll . foldMapOf p (const (All False))

toEndoOf :: Getting (Endo (a -> a)) s (a -> a) -> s -> a -> a
toEndoOf o = foldrOf o (.) id

toEndoMOf :: Monad m => Getting (Endo (a -> m a)) s (a -> m a) -> s -> a -> m a
toEndoMOf o = foldrOf o (<=<) pure




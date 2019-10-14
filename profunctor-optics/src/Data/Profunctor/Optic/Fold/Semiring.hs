module Data.Profunctor.Optic.Fold.Semiring where

import Data.Profunctor.Optic.Fold

import Data.Semigroup
import Data.Profunctor.Optic.Type 
import Data.Profunctor.Optic.Prelude

import Data.Profunctor.Optic.Getter (view, to)
import Data.Profunctor.Optic.Prism (_Just, filtering)
import Data.Foldable (traverse_)

import Data.Semiring
import Data.Semiring.Endomorphism


import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE


-- | Try to map a function lift this 'Traversal', failing if the 'Traversal' has no targets.
--
-- >>> failover (element 3) (*2) [1,2] :: Maybe [Int]
-- Nothing
--
-- >>> failover _Left (*2) (Right 4) :: Maybe (Either Int Int)
-- Nothing
--
-- >>> failover _Right (*2) (Right 4) :: Maybe (Either Int Int)
-- Just (Right 8)
--
-- @
-- 'failover' :: Alternative m => Traversal s t a b -> (a -> b) -> s -> m t
-- @
{-
failover :: Alternative m => LensLike ((,) Any) s t a b -> (a -> b) -> s -> m t
failover l afb s = case l ((,) (Any True) . afb) s of
  (Any True, t)  -> pure t
  (Any False, _) -> Applicative.empty
{-# INLINE failover #-}
-}


-- >>> polyOf folded id [1 .. (5 :: Int)]
-- 15
-- 
-- >>> polyOf folded id $ 1 :| [2 .. (5 :: Int)]
-- 15
--
-- >>> polyOf folded1 id $ 1 :| [2 .. (5 :: Int)]
-- 120
--
-- >>> polyOf (folded . folded1) id [(1 :: Int) :| [3,7], 1 :| [3,7]]
-- 42
--
-- >>> polyOf (both . folded1) id ((1 :: Int) :| [3,7], 1 :| [3,7])
-- 42
--
polyOf :: APoly r s a -> (a -> r) -> s -> r
polyOf = between (dstar runPoly) (ustar Poly)

-- | Right fold lift a 'Fold'.
-- >>> foldrOf'' folded (<>) (zero :: Int) [1..5]
-- 15
foldrOf :: APoly (Endo r) s a -> (a -> r -> r) -> r -> s -> r
foldrOf p f r = (`appEndo` r) . polyOf p (Endp . f)




{-

foldrOF p f g r s = (loweR r . lowerProD s) . foldMapOf' p (lifT g . lifT f)

loweR :: (Monoid a) => a -> End a -> a
loweR r (End f) = f r

lowerProD :: (Monoid a, Semiring a) => a -> End (End a) -> End a
lowerProD r (End f) = f $ lift r

lifT f = End . f

foo :: Int -> Int -> [Int] -> Int
foo = foldrOF folded (<>) prod

lift :: (Monoid a) => a -> End a
lift a = End (a <>)

lift' :: (Monoid a, Semiring a) => a -> End (End a)
lift' = liftProd . lift


lower' :: (Monoid a, Semiring a) => End (End a) -> a
lower' = lower . lowerProd

-- We can use the isomorphism between @End (End a)@ and @End a@ in order to reuse the multiplicative structure of @a@.
prod :: (Monoid a, Semiring a) => End a -> End a -> End a
prod f g = lift $ lower f >< lower g

liftProd :: (Monoid a, Semiring a) => End a -> End (End a)
liftProd a = End (a `prod`)

lowerProd :: (Monoid a, Semiring a) => End (End a) -> End a
lowerProd (End f) = f $ lift one
-}



{-

-- This is a weird function? Not constructing to incor
--TODO replace w/ Endo and use a separate Cayley somewhere else


-- >>> foldlOf'' folded (<>) [] ["hello"," world"]
-- "hello world"
--
-- >>> foldlOf'' folded1 (<>) "> " $ "hello" :| [" world"]
-- "> hello world"
foldlOf'' :: APoly (End (End c)) s a -> (c -> a -> c) -> c -> s -> c
foldlOf'' o f c0 s = foldrOf o (force f) (End id) s `appEnd` c0

force :: (c -> a -> c) -> a -> End c -> End c
force f x (End k) = End $ \z -> k $! f z x

--foldlOf'' :: (Monoid c, Semiring c) => FoldLike (End (End c)) s a -> c -> s -> c
foldlOf'' o c0 s = foldrOf o (force foo) (End $ id) s `appEnd` c0


foo :: (Monoid a, Semiring a) => End a -> End a -> End a
foo c d = lowerProd $ liftProd c >< liftProd d

foo'' c d = lower $ lift c `foo` lift d

foo' :: (Monoid a, Semiring a) => a -> a -> a
foo' c d = lower' $ lift' d >< lift' c

mul :: End (End Int) -> End (End Int)
mul = force foo $ End (const 5) -- id --lift one -- (lift (5::Int))
--mul = force (><) $ End (const 5) 
--mul = force (<>) $ End (const 5) 

mul5 :: Int -> Int
mul5 = lower' . mul . lift'


--harness f a b = lower $ f (lift a) (lift b)
harness f a b = lower' $ (force f (lift a) (lift' b))

harn a b f = lower' $ f (lift' a) (lift' b)

{-
lower $ lift (2::Int) >< lift (3::Int) -- 5!
lower' $ lift' (2::Int) >< lift' (3::Int) -- 6
lower $ lift (2::Int) <> lift (3::Int) -- 5
lower' $ lift' (2::Int) <> lift' (3::Int) -- 5
-}

liftProd :: (Monoid a, Semiring a) => End a -> End (End a)
liftProd a = End (a `prod`)

lowerProd :: (Monoid a, Semiring a) => End (End a) -> End a
lowerProd (End f) = f $ lift one


bar :: (Monoid a0, Semiring a0) => End a0 -> [End a0] -> End a0
bar = foldrOf folded prod

ok' = foldlOf'' folded (lift (1 :: Int))

out :: [Int] -> Int
out = lower . ok' . fmap lift
-}

{-
ok :: Foldable f => f (End Int) -> End Int
ok = foldlOf'' folded prod (lift one)

ok' :: Foldable f => f (End (End Int)) -> End (End Int)
ok' = foldlOf'' folded (lift' (1 :: Int))

-- >>> out [1..5]
-- 15
out :: [Int] -> Int
out = lower . ok . fmap lift

-- >>> out' [1..5]
-- 5
out' :: [Int] -> Int
out' = lower' . ok' . fmap lift'
-}




{-
-- | Find the innermost focus of a `Fold` that satisfies a predicate, if there is any.
--
findOf :: Folding (Endo (Maybe a)) s a -> (a -> Bool) -> s -> Maybe a
findOf o f =
  foldrOf o (\a -> maybe (if f a then Just a else Nothing) Just) Nothing


-- | The maximum of all foci of a `Fold`, if there is any.
--
maximumOf :: Ord a => Folding (Endo (Maybe a)) s a -> s -> Maybe a
maximumOf o = foldrOf o (\a -> Just . maybe a (max a)) Nothing

-- | The minimum of all foci of a `Fold`, if there is any.
--
minimumOf :: Ord a => Folding (Endo (Maybe a)) s a -> s -> Maybe a
minimumOf o = foldrOf o (\a -> Just . maybe a (min a)) Nothing
-}


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
maximumByOf :: Folding (Endo (Endo (Maybe a))) s a -> (a -> a -> Ordering) -> s -> Maybe a
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
minimumByOf :: Folding (Endo (Endo (Maybe a))) s a -> (a -> a -> Ordering) -> s -> Maybe a
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
-- 'findOf' :: 'Folding' ('Endo' ('Maybe' a)) s a -> (a -> 'Bool') -> s -> 'Maybe' a
-- 'findOf' o p = 'foldrOf' o (\a y -> if p a then 'Just' a else y) 'Nothing'
-- @
findOf :: Folding (Endo (Maybe a)) s a -> (a -> Bool) -> s -> Maybe a
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
-- 'findMOf' :: Monad m => 'Folding' ('Endo' (m ('Maybe' a))) s a -> (a -> m 'Bool') -> s -> m ('Maybe' a)
-- 'findMOf' o p = 'foldrOf' o (\a y -> p a >>= \x -> if x then return ('Just' a) else y) $ return 'Nothing'
-- @
findMOf :: Monad m => Folding (Endo (m (Maybe a))) s a -> (a -> m Bool) -> s -> m (Maybe a)
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
lookupOf :: Eq k => Folding (Endo (Maybe v)) s (k,v) -> k -> s -> Maybe v
lookupOf o k = foldrOf o (\(k',v) next -> if k == k' then Just v else next) Nothing
{-# INLINE lookupOf #-}
-}



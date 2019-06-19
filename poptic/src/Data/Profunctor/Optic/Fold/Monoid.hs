module Data.Profunctor.Optic.Fold.Monoid where

import Data.Monoid
import Data.Profunctor.Optic.Type 
import Data.Profunctor.Optic.Operator
import Data.Profunctor.Optic.Prelude

import Data.Profunctor.Optic.Fold.Semigroup
import Data.Profunctor.Optic.View (view, to)
import Data.Profunctor.Optic.Prism (_Just, filtering)
import Data.Foldable (traverse_)
--import Data.Functor.Const (Const(..))

import Data.DList (DList)
import qualified Data.DList as L

import Control.Monad ((<=<))
--import Control.Monad.Reader as Reader
--import Control.Monad.State as State

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
cloneFold :: Monoid r => AFold r s a -> Fold s a
cloneFold f = to $ \s -> getConst (f Const s)
-}



{-


-- | Folds over a `Foldable` container.
folded :: Foldable f => Monoid r => AFold r (f a) a
folded (Star Const) = undefined --Star $ Const . foldMap a
folded (Forget a) = Forget (foldMap a)

-- | Folds over a `Foldable` container.
--folded :: (Foldable f, Monoid r) => (a -> r) -> AFold r (f a) a
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
replicated :: Monoid r => Int -> AFold r s a
replicated i (Star (Const a)) = Star (Const (go i a))
  where go 0 _ = mempty
        go n x = x <> go (n - 1) x

-- | Builds a `Fold` using an unfold.
unfolded :: Monoid r => (s -> Maybe (a, s)) -> AFold r s a
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
-- Primitive Operators
---------------------------------------------------------------------

-- | Collects the foci of a `Fold` into a list.
toListOf :: AFold (DList a) s a -> s -> [a]
toListOf o = flip L.apply [] . foldMapOf o L.singleton 

toListOf' :: AFold (Prod (End [a])) s a -> s -> [a]
toListOf' o = foldrOf' o (:) []


---------------------------------------------------------------------
-- Derived Operators
---------------------------------------------------------------------


sumOf = foldMapOf

-- | Map each part of a structure viewed through a 'Lens', 'View',
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
-- 'productOf' :: 'Monoid' r    => 'Traversal0'' s a -> (a -> r) -> s -> r
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
productOf :: AFold (Prod r) s a -> (a -> r) -> s -> r
productOf o f = getProd . foldMapOf o (Prod . f)

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

foldOf :: AFold a s a -> s -> a
foldOf = flip foldMapOf id


-- @
-- toPureOf :: Fold s a -> s -> [a]
-- toPureOf :: (Applicative f, Monoid (f a)) => Fold s a -> s -> f a
-- toPureOf :: Applicative f => Over s t a b -> s -> f a
-- @
toPureOf :: Applicative f => AFold (f a) s a -> s -> f a
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
-- ('^..') :: s -> 'Affine'' s a    -> [a]
-- @
(^..) :: s -> AFold (DList a) s a -> [a]
(^..) = flip toListOf
{-# INLINE (^..) #-}



foldrOf' :: AFold (Prod (End c)) s a -> (a -> c -> c) -> c -> s -> c
foldrOf' p f r = (`appEnd` r) . productOf p (End . f)


-- | Right fold over a 'Fold'.
-- >>> foldrOf'' folded (<>) (zero :: Int) [1..5]
-- 15
foldrOf :: AFold (End c) s a -> (a -> c -> c) -> c -> s -> c
foldrOf p f r = (`appEnd` r) . foldMapOf p (End . f)

-- >>> endOf folded Prod [1..(5 :: Int)]
-- Prod {getProd = 120}
endOf :: Monoid c => AFold (End c) s a -> (a -> c) -> s -> c
endOf p f = lower . foldMapOf p (lift . f)

endOf' :: (Monoid c, Semiring c) => AFold (End (End c)) s a -> (a -> c) -> s -> c
endOf' p f = lower' . foldMapOf p (lift' . f)


foldrOF p f g r s = (loweR r . lowerProD s) . foldMapOf' p (lifT g . lifT f)

loweR :: (Monoid a) => a -> End a -> a
loweR r (End f) = f r

lowerProD :: (Monoid a, Semiring a) => a -> End (End a) -> End a
lowerProD r (End f) = f $ lift r

lifT f = End . f

foo :: Int -> Int -> [Int] -> Int
foo = foldrOF folded (<>) prod

{-
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


-- >>> foldrOf' folded (><) (one :: Int) [1..5]
-- 120
--foldrOf' :: AFold (Prod (End c)) s a -> (a -> c -> c) -> c -> s -> c
--foldrOf' p f r = (`appEnd` r) . productOf p (End . f)

-- | Left fold over a 'Fold'. 
foldlOf :: AFold (Dual (Endo c)) s a -> (c -> a -> c) -> c -> s -> c
foldlOf p f r = (`appEndo` r) . getDual . foldMapOf p (Dual . Endo . flip f)

-- foldlOf' folded (<>) [] ["hi","THere"]
foldlOf' :: AFold (End (End c)) s a -> (c -> a -> c) -> c -> s -> c
foldlOf' o f c0 s = foldrOf o (force f) (End id) s `appEnd` c0

force :: (c -> a -> c) -> a -> End c -> End c
force f x (End k) = End $ \z -> k $! f z x
--force f x (End k) = (End k) <> (End $ \z -> f $! z x)

{-
--foldlOf'' :: (Monoid c, Semiring c) => AFold (End (End c)) s a -> c -> s -> c
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


-- | Fold over the elements of a structure, associating to the left, but strictly.
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


-- | Obtain the maximum element (if any) targeted by a 'Fold', 'Traversal', 'Lens', 'Iso',
-- or 'View' according to a user supplied 'Ordering'.
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
-- 'maximumByOf' :: 'View' s a       -> (a -> a -> 'Ordering') -> s -> 'Maybe' a
-- 'maximumByOf' :: 'Fold' s a       -> (a -> a -> 'Ordering') -> s -> 'Maybe' a
-- 'maximumByOf' :: 'Iso'' s a       -> (a -> a -> 'Ordering') -> s -> 'Maybe' a
-- 'maximumByOf' :: 'Lens'' s a      -> (a -> a -> 'Ordering') -> s -> 'Maybe' a
-- 'maximumByOf' :: 'Traversal'' s a -> (a -> a -> 'Ordering') -> s -> 'Maybe' a
-- @
maximumByOf :: AFold (Endo (Endo (Maybe a))) s a -> (a -> a -> Ordering) -> s -> Maybe a
maximumByOf o cmp = foldlOf' o mf Nothing where
  mf Nothing y = Just $! y
  mf (Just x) y = Just $! if cmp x y == GT then x else y
{-# INLINE maximumByOf #-}



toEndoOf :: AFold (Endo (a -> a)) s (a -> a) -> s -> a -> a
toEndOf o = foldrOf o (.) (End id)

toEndoMOf :: Monad m => AFold (Endo (a -> m a)) s (a -> m a) -> s -> a -> m a
toEndoMOf o = foldrOf o (<=<) pure

-- | Traverse the foci of a `Fold`, discarding the results.
traverseOf_
  :: Applicative f 
  => AFold (Endo (f ())) s a -> (a -> f x) -> s -> f ()
traverseOf_ p f = foldrOf p (\a f' -> (() <$) (f a) *> f') $ pure ()

sequenceOf_
  :: Applicative f 
  => AFold (Endo (f ())) s (f a) -> s -> f ()
sequenceOf_ p = traverseOf_ p id
-}


allOf :: AFold (Prod Bool) s a -> (a -> Bool) -> s -> Bool
allOf o f = productOf o f

anyOf :: AFold Bool s a -> (a -> Bool) -> s -> Bool
anyOf = sumOf


{-
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
-- 'lengthOf' :: 'Getter' s a     -> s -> 'Int'
-- 'lengthOf' :: 'Fold' s a       -> s -> 'Int'
-- 'lengthOf' :: 'Lens'' s a      -> s -> 'Int'
-- 'lengthOf' :: 'Iso'' s a       -> s -> 'Int'
-- 'lengthOf' :: 'Traversal'' s a -> s -> 'Int'
-- @
lengthOf :: Getting (Endo (Endo Int)) s a -> s -> Int
lengthOf l = foldlOf' l (\a _ -> a + 1) 0
{-# INLINE lengthOf #-}
-}
lengthOf :: Num r => AFold (Sum r) s a -> s -> r
lengthOf o = getSum . foldMapOf o (const (Sum 1))

nullOf :: AFold (Prod Bool) s a -> s -> Bool
nullOf o = allOf o (const False)

-- | Whether a `Fold` contains a given element.
elemOf :: Eq a => AFold Bool s a -> a -> s -> Bool
elemOf p a = anyOf p (== a)

-- | Whether a `Fold` not contains a given element.
notElemOf :: Eq a => AFold (Prod Bool) s a -> a -> s -> Bool
notElemOf p a = allOf p (/= a)

-- | Determines whether a `Fold` has at least one focus.
--
has :: AFold Bool s a -> s -> Bool
has p = foldMapOf p (const True)

-- | Determines whether a `Fold` does not have a focus.
--
hasnt :: AFold (Prod Bool) s a -> s -> Bool
hasnt p = productOf p (const False)




module Data.Profunctor.Optic.Fold where

import Control.Foldl (EndoM(..))
import Control.Monad ((<=<))
import Data.Foldable (Foldable, foldMap, traverse_)
import Data.Functor.Foldable (Recursive, Base)
import Data.Monoid
import Data.Prd (Prd(..), Min(..), Max(..))
import Data.Prd.Lattice (Lattice(..))
import Data.Semiring (Semiring(..))
import Data.Profunctor.Optic.Prelude hiding (min, max, joins)
import Data.Profunctor.Optic.Traversal
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.View (to, view, cloneView)
import qualified Control.Foldl as L
import qualified Data.Functor.Foldable as F
import qualified Data.Prd as Prd
import qualified Data.Semiring as Rng
import qualified Prelude as Pre

---------------------------------------------------------------------
-- 'Fold'
---------------------------------------------------------------------

-- | Transform a Van Laarhoven 'Fold' into a profunctor 'Fold'.
--
foldVL :: (forall f. Applicative f => (a -> f b) -> s -> f t) -> Fold s a
foldVL f = coercer . lift f . coercer
{-# INLINE foldVL #-}

-- | Obtain a 'Fold' using a 'Traversable' functor.
--
-- @
-- 'folded' f ≡ 'lift' 'traverse' . 'to' f
-- @
--
folded :: Traversable f => (s -> a) -> Fold (f s) a
folded f = traversed . to f
{-# INLINE folded #-}

-- | Obtain a 'Fold' by lifting an operation that returns a 'Foldable' result.
--
-- @ 
-- 'folding' ('toListOf' o) ≡ o
-- @
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

-- | TODO: Document
--
folding' :: Foldable f => Fold (f a) a
folding' = folding id
{-# INLINE folding' #-}

-- | Build a 'Fold' from a 'View'.
--
toFold :: AView s a -> Fold s a
toFold = to . view
{-# INLINE toFold #-}

-- | Build a monoidal 'View' from a 'Fold'.
--
fromFold :: Monoid a => AFold a s a -> View s a
fromFold = cloneView
{-# INLINE fromFold #-}

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
import Data.Functor.Foldable (ListF(..))

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

-- | Map parts of a structure to a monoid and combine the results.
--
-- @
-- 'Data.Foldable.foldMap' = 'foldMapOf' 'folding''
-- @
--
-- >>> foldMapOf both id (["foo"], ["bar", "baz"])
-- ["foo","bar","baz"]
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

-- | Collect the foci of a `Fold` into a list.
--
toListOf :: AFold (Endo [a]) s a -> s -> [a]
toListOf o = foldsr o (:) []

-- | TODO: Document
--
foldOf :: Monoid a => AFold a s a -> s -> a
foldOf = flip foldMapOf id

-- ^ @
-- toPureOf :: Fold s a -> s -> [a]
-- toPureOf :: Applicative f => Setter s t a b -> s -> f a
-- @
toPureOf :: Applicative f => Monoid (f a) => AFold (f a) s a -> s -> f a
toPureOf o = foldMapOf o pure

---------------------------------------------------------------------
-- Common 'Fold's
---------------------------------------------------------------------

-- | Compute the result of an expression in a unital semiring.
--
-- @ 
-- 'unital' ≡ 'summed' . 'multiplied'
-- @
--
-- >>> foldOf unital [[1,2], [3,4 :: Int]]
-- 14
--
unital :: Foldable f => Foldable g => Monoid r => Semiring r => AFold r (f (g a)) a
unital = summed . multiplied -- afold Rng.unital

-- | Compute the monoidal summed of a 'Fold'.
--
-- >>> 1 <> 2 <> 3 <> 4 :: Int
-- 10
--
-- >>> foldOf summed [1,2,3,4 :: Int]
-- 10
--
summed :: Foldable f => Monoid r => AFold r (f a) a
summed = afold foldMap

-- | Compute the multiplied of a 'Fold'.
--
-- >>> 1 >< 2 >< 3 >< 4 :: Int
-- 24
--
-- >>> foldOf multiplied [1,2,3,4 :: Int]
-- 24
--
-- 'summed' and 'multiplied' compose just as they do in arithmetic:
--
-- >>> 1 >< 2 <> 3 >< 4 :: Int
-- 14
--
-- >>> foldOf (summed . multiplied) [[1,2], [3,4 :: Int]]
-- 14
--
-- >>> 1 <> 2 >< 3 <> 4 :: Int
-- 21
--
-- >>> foldOf (multiplied . summed) [[1,2], [3,4 :: Int]]
-- 21
--
multiplied :: Foldable f => Monoid r => Semiring r => AFold r (f a) a
multiplied = afold Rng.product

-- | Precompose with a Moore machine.
--
premapped :: Handler b a -> L.Fold a c -> L.Fold b c
premapped o (L.Fold h z k) = L.Fold (foldsl' o h) z k

-- | Precompose with an effectful Moore machine.
--
premappedM :: Monad m => HandlerM m b a -> L.FoldM m a c -> L.FoldM m b c
premappedM o (L.FoldM h z k) = L.FoldM (foldsM' o h) z k

---------------------------------------------------------------------
-- Derived operators
---------------------------------------------------------------------

infixl 8 ^..

-- | Infix version of 'toListOf'.
--
-- @
-- 'Data.Foldable.toList' xs ≡ xs '^..' 'folded'
-- ('^..') ≡ 'flip' 'toListOf'
-- @
--
-- >>> [[1,2], [3 :: Int]] ^.. id
-- [[[1,2], [3]]]
-- >>> [[1,2], [3 :: Int]] ^.. traversed
-- [[1,2], [3]]
-- >>> [[1,2], [3 :: Int]] ^.. traversed . traversed
-- [1,2,3]
--
-- >>> (1,2) ^.. bitraversed
-- [1,2]
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
--
(^..) :: s -> AFold (Endo [a]) s a -> [a]
(^..) = flip toListOf
{-# INLINE (^..) #-}

-- | Right fold lift a 'Fold'.
--
-- >>> foldsr'' folded (<>) (zero :: Int) [1..5]
-- 15
--
foldsr :: AFold (Endo r) s a -> (a -> r -> r) -> r -> s -> r
foldsr p f r = (`appEndo` r) . foldMapOf p (Endo . f)

-- | Left fold lift a 'Fold'.
--
foldsl :: AFold (Dual (Endo c)) s a -> (c -> a -> c) -> c -> s -> c
foldsl p f r = (`appEndo` r) . getDual . foldMapOf p (Dual . Endo . flip f)

-- | Fold lift the elements of a structure, associating to the left, but strictly.
--
-- @
-- 'Data.Foldable.foldl'' ≡ 'foldsl'' 'folded'
-- @
--
-- @
-- 'foldsl'' :: 'Iso'' s a        -> (c -> a -> c) -> c -> s -> c
-- 'foldsl'' :: 'Lens'' s a       -> (c -> a -> c) -> c -> s -> c
-- 'foldsl'' :: 'View' s a        -> (c -> a -> c) -> c -> s -> c
-- 'foldsl'' :: 'Fold' s a        -> (c -> a -> c) -> c -> s -> c
-- 'foldsl'' :: 'Traversal'' s a  -> (c -> a -> c) -> c -> s -> c
-- 'foldsl'' :: 'Traversal0'' s a -> (c -> a -> c) -> c -> s -> c
-- @
--
foldsl' :: AFold (Endo (Endo c)) s a -> (c -> a -> c) -> c -> s -> c
foldsl' o f c s = foldsr o f' (Endo id) s `appEndo` c
  where f' x (Endo k) = Endo $ \z -> k $! f z x
{-# INLINE foldsl' #-}

-- | A strict monadic left fold.
--
foldsM' :: Monad m => AFold (Endo (EndoM m r)) s a -> (r -> a -> m r) -> r -> s -> m r
foldsM' o f c s = foldsr o f' mempty s `appEndoM` c
  where f' x (EndoM k) = EndoM $ \z -> (f $! z) x >>= k

-- | TODO: Document
--
endo :: AFold (Endo (a -> a)) s (a -> a) -> s -> a -> a
endo o = foldsr o (.) id

-- | TODO: Document
--
endoM :: Monad m => AFold (Endo (a -> m a)) s (a -> m a) -> s -> a -> m a
endoM o = foldsr o (<=<) pure

-- | Determine whether a `Fold` has at least one focus.
--
has :: AFold Any s a -> s -> Bool
has p = getAny . foldMapOf p (const (Any True))

-- | Determine whether a `Fold` does not have a focus.
--
hasnt :: AFold All s a -> s -> Bool
hasnt p = getAll . foldMapOf p (const (All False))

-- | TODO: Document
--
nulls :: AFold All s a -> s -> Bool
nulls o = all o (const False)

-- | Find the minimum of a totally ordered set. 
--
min :: Ord a => AFold (Endo (Endo a)) s a -> a -> s -> a
min o = foldsl' o Pre.min

-- | Find the maximum of a totally ordered set.
--
max :: Ord a => AFold (Endo (Endo a)) s a -> a -> s -> a
max o = foldsl' o Pre.max

-- | Find the (partial) minimum of a partially ordered set.
--
pmin :: Eq a => Prd a => AFold (Endo (EndoM Maybe a)) s a -> a -> s -> Maybe a
pmin o = foldsM' o Prd.pmin

-- | Find the (partial) minimum of a partially ordered set.
--
pmax :: Eq a => Prd a => AFold (Endo (EndoM Maybe a)) s a -> a -> s -> Maybe a
pmax o = foldsM' o Prd.pmax

-- | Find the (partial) joins of a sublattice. 
--
joins :: Lattice a => AFold (Endo (Endo a)) s a -> a -> s -> a
joins o = foldsl' o (\/)

-- | Find the joins of a sublattice or return the bottom element.
--
joins' :: Lattice a => Min a => AFold (Endo (Endo a)) s a -> s -> a
joins' o = joins o minimal

-- | Find the (partial) meets of a sublattice.
--
meets :: Lattice a => AFold (Endo (Endo a)) s a -> a -> s -> a
meets o = foldsl' o (/\)

-- | Find the meets of a sublattice or return the top element.
--
meets' :: Lattice a => Max a => AFold (Endo (Endo a)) s a -> s -> a
meets' o = meets o maximal

-- | TODO: Document
--
all :: AFold All s a -> (a -> Bool) -> s -> Bool
all o p = getAll . foldMapOf o (All . p)

-- | TODO: Document
--
any :: AFold Any s a -> (a -> Bool) -> s -> Bool
any o p = getAny . foldMapOf o (Any . p)

-- | Determine whether a `Fold` contains a given element.
elem :: Eq a => AFold Any s a -> a -> s -> Bool
elem p a = any p (== a)

-- | Determine whether a `Fold` not contains a given element.
notElem :: Eq a => AFold All s a -> a -> s -> Bool
notElem p a = all p (/= a)


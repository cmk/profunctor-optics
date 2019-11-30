{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Profunctor.Optic.Fold (
    -- * Fold & Ixfold
    Fold
  , Ixfold
  , fold_
  , folding 
  , foldVl
  , toFold
  , cloneFold
    -- * Carriers
  , FoldRep
  , AFold
  , AIxfold
  , afold  
    -- * Primitive operators
  , foldMapOf
  , ixfoldMapOf
  , pureOf
  , productOf
    -- * Optics
  , folded
  , folded_ 
  , unital
  , summed
  , multiplied 
    -- * Operators
  , (^..)
  , folds
  , foldsr
  , foldsl
  , foldsl'
  , lists
  , traverses_
  , concats
  , finds
  , has
  , hasnt 
  , nulls
  , asums
  , joins
  , joins'
  , meets
  , meets'
  , pelem
    -- * Indexed operators
  , (^%%)
  , ixfoldsr
  , ixfoldsrFrom
  , ixfoldsl
  , ixfoldslFrom
  , ixfoldsrM
  , ixfoldsrMFrom
  , ixfoldslM
  , ixfoldslMFrom
  , ixlists
  , ixlistsFrom
  , ixtraverses_
  , ixconcats
  , ixfinds
    -- * Auxilliary Types
  , All, Any
) where

import Control.Applicative
import Control.Monad ((<=<), void)
import Control.Monad.Reader as Reader hiding (lift)
import Control.Monad.State as State hiding (lift)
import Data.Foldable (Foldable, foldMap, traverse_)
import Data.Maybe
import Data.Monoid hiding (All(..), Any(..))
import Data.Prd (Prd(..), Min(..), Max(..))
import Data.Prd.Lattice (Lattice(..))
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Prism (right, just)
import Data.Profunctor.Optic.Type
import Data.Profunctor.Optic.View (AView, to, from, primViewOf, view, cloneView)
import Data.Semiring (Semiring(..), Prod(..))
import qualified Data.Prd as Prd
import qualified Data.Semiring as Rng

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> import Control.Exception hiding (catches)
-- >>> import Data.Functor.Identity
-- >>> import Data.List.Index
-- >>> import Data.Map as Map
-- >>> import Data.Sequence as Seq hiding ((><))
-- >>> import Data.Maybe
-- >>> import Data.Monoid
-- >>> import Data.Semiring hiding (unital,nonunital,presemiring)
-- >>> :load Data.Profunctor.Optic
-- >>> let ixtraversed :: Ixtraversal Int [a] [b] a b ; ixtraversed = ixtraversalVl itraverse

---------------------------------------------------------------------
-- 'Fold' & 'Ixfold'
---------------------------------------------------------------------

type FoldRep r = Star (Const r)

type AFold r s a = Optic' (FoldRep r) s a

type AIxfold r i s a = IndexedOptic' (FoldRep r) i s a

-- | Obtain a 'Fold' directly.
--
-- @ 
-- 'fold_' ('lists' o) ≡ o
-- 'fold_' f ≡ 'to' f . 'foldVl' 'traverse_'
-- 'fold_' f ≡ 'coercer' . 'lmap' f . 'lift' 'traverse_'
-- @
--
-- See 'Data.Profunctor.Optic.Property'.
--
-- This can be useful to repn operations from @Data.List@ and elsewhere into a 'Fold'.
--
-- >>> [1,2,3,4] ^.. fold_ tail
-- [2,3,4]
--
fold_ :: Foldable f => (s -> f a) -> Fold s a
fold_ f = to f . foldVl traverse_
{-# INLINE fold_ #-}

-- | Obtain a 'Fold' from a 'Traversable' functor.
--
-- @
-- 'folding' f ≡ 'traversed' . 'to' f
-- 'folding' f ≡ 'foldVl' 'traverse' . 'to' f
-- @
--
folding :: Traversable f => (s -> a) -> Fold (f s) a
folding f = foldVl traverse . to f
{-# INLINE folding #-}

-- | Obtain a 'Fold' from a Van Laarhoven 'Fold'.
--
foldVl :: (forall f. Applicative f => (a -> f b) -> s -> f t) -> Fold s a
foldVl f = coercer . repn f . coercer
{-# INLINE foldVl #-}

-- | Obtain a 'Fold' from a 'View' or 'AFold'.
--
toFold :: AView s a -> Fold s a
toFold = to . view
{-# INLINE toFold #-}

-- | TODO: Document
--
afold :: ((a -> r) -> s -> r) -> AFold r s a
afold o = Star #. (Const #.) #. o .# (getConst #.) .# runStar
{-# INLINE afold #-}

-- | Obtain a 'Fold' from a 'AFold'.
--
cloneFold :: Monoid a => AFold a s a -> View s a
cloneFold = cloneView
{-# INLINE cloneFold #-}

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | Map an optic to a monoid and combine the results.
--
-- @
-- 'Data.Foldable.foldMap' = 'foldMapOf' 'folded_''
-- @
--
-- >>> foldMapOf both id (["foo"], ["bar", "baz"])
-- ["foo","bar","baz"]
--
-- >>> :t foldMapOf . fold_
-- foldMapOf . fold_
--   :: (Monoid r, Foldable f) => (s -> f a) -> (a -> r) -> s -> r
--
-- >>> :t foldMapOf traversed
-- foldMapOf traversed
--   :: (Monoid r, Traversable f) => (a -> r) -> f a -> r
--
-- >>> :t foldMapOf left
-- foldMapOf left :: Monoid r => (a -> r) -> (a + c) -> r
--
-- >>> :t foldMapOf first
-- foldMapOf first :: Monoid r => (a -> r) -> (a, c) -> r
--
-- >>> :t foldMapOf $ selected even
-- foldMapOf $ selected even
--   :: (Monoid r, Integral a) => (b -> r) -> (a, b) -> r
--
-- >>> :t flip foldMapOf Seq.singleton
-- flip foldMapOf Seq.singleton :: AFold (Seq a) s a -> s -> Seq a
--
foldMapOf :: Monoid r => AFold r s a -> (a -> r) -> s -> r
foldMapOf = primViewOf
{-# INLINE foldMapOf #-}

-- | TODO: Document
--
-- >>> :t flip ixfoldMapOf Map.singleton
-- flip ixfoldMapOf Map.singleton
--   :: AIxfold (Map i a) i s a -> i -> s -> Map i a
--
ixfoldMapOf :: AIxfold r i s a -> (i -> a -> r) -> i -> s -> r
ixfoldMapOf o f = curry $ primViewOf o (uncurry f)
{-# INLINE ixfoldMapOf #-}

-- | TODO: Document
-- 
-- @
-- pureOf :: Fold s a -> s -> [a]
-- pureOf :: Applicative f => Setter s t a b -> s -> f a
-- @
--
pureOf :: Applicative f => Monoid (f a) => AFold (f a) s a -> s -> f a
pureOf o = foldMapOf o pure
{-# INLINE pureOf #-}

-- | Compute the semiring product of the foci of an optic.
--
-- For semirings without a multiplicative unit this is equivalent to @const mempty@:
--
-- >>> productOf folded Just [1..(5 :: Int)]
-- Just 0
--
-- In this situation you most likely want to use 'product1Of'.
--
productOf :: Monoid r => Semiring r => AFold (Prod r) s a -> (a -> r) -> s -> r
productOf o p = getProd . foldMapOf o (Prod . p)
{-# INLINE productOf #-}

---------------------------------------------------------------------
-- Common folds
---------------------------------------------------------------------

-- | Obtain a 'Fold' from a 'Traversable' functor.
--
folded :: Traversable f => Fold (f a) a
folded = folding id
{-# INLINE folded #-}

-- | The canonical 'Fold'.
--
-- @
-- 'Data.Foldable.foldMap' ≡ 'foldMapOf' 'folded_''
-- @
--
folded_ :: Foldable f => Fold (f a) a
folded_ = fold_ id
{-# INLINE folded_ #-}

-- | Expression in a unital semiring 
--
-- @ 
-- 'unital' ≡ 'summed' . 'multiplied'
-- @
--
-- >>> folds unital [[1,2], [3,4 :: Int]]
-- 14
--
-- For semirings without a multiplicative unit this is 
-- equivalent to @const mempty@:
--
-- >>> folds unital $ (fmap . fmap) Just [[1,2], [3,4 :: Int]]
-- Just 0
--
-- In this situation you most likely want to use 'nonunital'.
--
unital :: Foldable f => Foldable g => Monoid r => Semiring r => AFold r (f (g a)) a
unital = summed . multiplied
{-# INLINE unital #-}

-- | Monoidal sum of a foldable collection.
--
-- >>> 1 <> 2 <> 3 <> 4 :: Int
-- 10
-- >>> folds summed [1,2,3,4 :: Int]
-- 10
--
-- 'summed' and 'multiplied' compose just as they do in arithmetic:
--
-- >>> 1 >< 2 <> 3 >< 4 :: Int
-- 14
-- >>> folds (summed . multiplied) [[1,2], [3,4 :: Int]]
-- 14
-- >>> (1 <> 2) >< (3 <> 4) :: Int
-- 21
-- >>> folds (multiplied . summed) [[1,2], [3,4 :: Int]]
-- 21
--
summed :: Foldable f => Monoid r => AFold r (f a) a
summed = afold foldMap
{-# INLINE summed #-}

-- | Semiring product of a foldable collection.
--
-- >>> 1 >< 2 >< 3 >< 4 :: Int
-- 24
-- >>> folds multiplied [1,2,3,4 :: Int]
-- 24
--
-- For semirings without a multiplicative unit this is 
-- equivalent to @const mempty@:
--
-- >>> folds multiplied $ fmap Just [1..(5 :: Int)]
-- Just 0
--
-- In this situation you most likely want to use 'multiplied1'.
--
multiplied :: Foldable f => Monoid r => Semiring r => AFold r (f a) a
multiplied = afold Rng.product
{-# INLINE multiplied #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

infixl 8 ^..

-- | Infix version of 'lists'.
--
-- @
-- 'Data.Foldable.toList' xs ≡ xs '^..' 'folding'
-- ('^..') ≡ 'flip' 'lists'
-- @
--
-- >>> [[1,2], [3 :: Int]] ^.. id
-- [[[1,2],[3]]]
-- >>> [[1,2], [3 :: Int]] ^.. traversed
-- [[1,2],[3]]
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
-- ('^..') :: s -> 'Affine'' s a    -> [a]
-- @
--
(^..) :: s -> AFold (Endo [a]) s a -> [a]
(^..) = flip lists
{-# INLINE (^..) #-}


-- | TODO: Document
--
folds :: Monoid a => AFold a s a -> s -> a
folds = flip foldMapOf id
{-# INLINE folds #-}

-- | Right fold over an optic.
--
-- >>> foldsr folded (<>) 0 [1..5::Int]
-- 15
--
foldsr :: AFold (Endo r) s a -> (a -> r -> r) -> r -> s -> r
foldsr o f r = (`appEndo` r) . foldMapOf o (Endo . f)
{-# INLINE foldsr #-}

-- | Left fold over an optic.
--
foldsl :: AFold (Dual (Endo r)) s a -> (r -> a -> r) -> r -> s -> r
foldsl o f r = (`appEndo` r) . getDual . foldMapOf o (Dual . Endo . flip f)
{-# INLINE foldsl #-}

-- | Fold repn the elements of a structure, associating to the left, but strictly.
--
-- @
-- 'Data.Foldable.foldl'' ≡ 'foldsl'' 'folding'
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
foldsl' :: AFold (Endo (Endo r)) s a -> (r -> a -> r) -> r -> s -> r
foldsl' o f r s = foldsr o f' (Endo id) s `appEndo` r
  where f' x (Endo k) = Endo $ \z -> k $! f z x
{-# INLINE foldsl' #-}

-- | Collect an applicative over the foci of an optic.
--
-- >>> traverses_ both putStrLn ("hello","world")
-- hello
-- world
--
-- @
-- 'Data.Foldable.traverse_' ≡ 'traverses_' 'folded'
-- @
--
traverses_ :: Applicative f => AFold (Endo (f ())) s a -> (a -> f r) -> s -> f ()
traverses_ p f = foldsr p (\a fu -> void (f a) *> fu) (pure ())
{-# INLINE traverses_ #-}

-- | Collect the foci of an optic into a list.
--
lists :: AFold (Endo [a]) s a -> s -> [a]
lists o = foldsr o (:) []
{-# INLINE lists #-}

-- | Map a function over all the foci of an optic and concatenate the resulting lists.
--
-- >>> concats both (\x -> [x, x + 1]) (1,3)
-- [1,2,3,4]
--
-- @
-- 'concatMap' ≡ 'concats' 'folded'
-- @
--
concats :: AFold [r] s a -> (a -> [r]) -> s -> [r]
concats = foldMapOf
{-# INLINE concats #-}

-- | Find the first focus of an optic that satisfies a predicate, if one exists.
--
-- >>> finds both even (1,4)
-- Just 4
--
-- >>> finds folded even [1,3,5,7]
-- Nothing
--
-- @
-- 'Data.Foldable.find' ≡ 'finds' 'folded'
-- @
--
finds :: AFold (Endo (Maybe a)) s a -> (a -> Bool) -> s -> Maybe a
finds o f = foldsr o (\a y -> if f a then Just a else y) Nothing
{-# INLINE finds #-}

-- | Determine whether an optic has at least one focus.
--
has :: AFold Any s a -> s -> Bool
has o = foldMapOf o (const True)
{-# INLINE has #-}

-- | Determine whether an optic does not have a focus.
--
hasnt :: AFold All s a -> s -> Bool
hasnt o = productOf o (const False)
{-# INLINE hasnt #-}

-- | TODO: Document
--
nulls :: AFold All s a -> s -> Bool
nulls o = productOf o (const False)
{-# INLINE nulls #-}

-- | The sum of a collection of actions, generalizing 'concatOf'.
--
-- >>> asums both ("hello","world")
-- "helloworld"
--
-- >>> asums both (Nothing, Just "hello")
-- Just "hello"
--
-- @
-- 'asum' ≡ 'asums' 'folded'
-- @
--
asums :: Alternative f => AFold (Endo (Endo (f a))) s (f a) -> s -> f a
asums o = foldsl' o (<|>) empty
{-# INLINE asums #-}

-- | Compute the join of the foci of an optic. 
--
joins :: Lattice a => AFold (Endo (Endo a)) s a -> a -> s -> a
joins o = foldsl' o (\/)
{-# INLINE joins #-}

-- | Compute the join of the foci of an optic including a least element.
--
joins' :: Lattice a => Min a => AFold (Endo (Endo a)) s a -> s -> a
joins' o = joins o minimal
{-# INLINE joins' #-}

-- | Compute the meet of the foci of an optic .
--
meets :: Lattice a => AFold (Endo (Endo a)) s a -> a -> s -> a
meets o = foldsl' o (/\)
{-# INLINE meets #-}

-- | Compute the meet of the foci of an optic including a greatest element.
--
meets' :: Lattice a => Max a => AFold (Endo (Endo a)) s a -> s -> a
meets' o = meets o maximal
{-# INLINE meets' #-}

-- | Determine whether the foci of an optic contain an element equivalent to a given element.
--
pelem :: Prd a => AFold Any s a -> a -> s -> Bool
pelem o a = foldMapOf o (Prd.=~ a)
{-# INLINE pelem #-}

------------------------------------------------------------------------------
-- Indexed operators
------------------------------------------------------------------------------

infixl 8 ^%%

-- | Infix version of 'ixlists'.
--
(^%%) :: Monoid i => s -> AIxfold (Endo [(i, a)]) i s a -> [(i, a)]
(^%%) = flip ixlists
{-# INLINE (^%%) #-}

-- | Indexed right fold over an indexed optic.
--
-- @
-- 'foldsr' o ≡ 'ixfoldsr' o '.' 'const'
-- @
--
-- >>> ixfoldsr ixtraversed (\i a -> ((show i ++ ":" ++ show a ++ ", ") ++)) [] [1,3,5,7,9]
-- "0:1, 1:3, 2:5, 3:7, 4:9, "
--
ixfoldsr :: Monoid i => AIxfold (Endo r) i s a -> (i -> a -> r -> r) -> r -> s -> r
ixfoldsr o f = ixfoldsrFrom o f mempty
{-# INLINE ixfoldsr #-}

-- | Indexed right fold over an indexed optic, using an initial index value.
--
ixfoldsrFrom :: AIxfold (Endo r) i s a -> (i -> a -> r -> r) -> i -> r -> s -> r
ixfoldsrFrom o f i r = (`appEndo` r) . ixfoldMapOf o (\i -> Endo . f i) i
{-# INLINE ixfoldsrFrom #-}

-- | Indexed left fold over an indexed optic.
--
-- @
-- 'foldsl' ≡ 'ixfoldsl' '.' 'const'
-- @
--
ixfoldsl :: Monoid i => AIxfold (Dual (Endo r)) i s a -> (i -> r -> a -> r) -> r -> s -> r
ixfoldsl o f = ixfoldslFrom o f mempty 
{-# INLINE ixfoldsl #-}

-- | Indexed left fold over an indexed optic, using an initial index value.
--
ixfoldslFrom :: AIxfold (Dual (Endo r)) i s a -> (i -> r -> a -> r) -> i -> r -> s -> r
ixfoldslFrom o f i r = (`appEndo` r) . getDual . ixfoldMapOf o (\i -> Dual . Endo . flip (f i)) i
{-# INLINE ixfoldslFrom #-}

-- | Indexed monadic right fold over an indexed optic.
--
-- @
-- 'foldsrM' ≡ 'ixfoldrM' '.' 'const'
-- @
--
ixfoldsrM :: Monoid i => Monad m => AIxfold (Dual (Endo (r -> m r))) i s a -> (i -> a -> r -> m r) -> r -> s -> m r
ixfoldsrM o f z0 xs = ixfoldsl o f' return xs z0
  where f' i k x z = f i x z >>= k
{-# INLINE ixfoldsrM #-}

-- | Indexed monadic right fold over an 'Ixfold', using an initial index value.
--
ixfoldsrMFrom :: Monad m => AIxfold (Dual (Endo (r -> m r))) i s a -> (i -> a -> r -> m r) -> i -> r -> s -> m r
ixfoldsrMFrom o f i z0 xs = ixfoldslFrom o f' i return xs z0
  where f' i k x z = f i x z >>= k
{-# INLINE ixfoldsrMFrom #-}

-- | Indexed monadic left fold over an indexed optic.
--
-- @
-- 'foldslM' ≡ 'ixfoldslM' '.' 'const'
-- @
--
ixfoldslM :: Monoid i => Monad m => AIxfold (Endo (r -> m r)) i s a -> (i -> r -> a -> m r) -> r -> s -> m r
ixfoldslM o f z0 xs = ixfoldsr o f' return xs z0
  where f' i x k z = f i z x >>= k
{-# INLINE ixfoldslM #-}

-- | Indexed monadic left fold over an indexed optic, using an initial index value.
--
ixfoldslMFrom :: Monad m => AIxfold (Endo (r -> m r)) i s a -> (i -> r -> a -> m r) -> i -> r -> s -> m r
ixfoldslMFrom o f i z0 xs = ixfoldsrFrom o f' i return xs z0
  where f' i x k z = f i z x >>= k
{-# INLINE ixfoldslMFrom #-}

-- | Extract the key-value pairs from the foci of an indexed optic.
--
-- @
-- 'lists' l ≡ 'map' 'snd' '.' 'ixlists' l
-- @
--
ixlists :: Monoid i => AIxfold (Endo [(i, a)]) i s a -> s -> [(i, a)]
ixlists o = ixfoldsr o (\i a -> ((i,a):)) []
{-# INLINE ixlists #-}

-- | Extract key-value pairs from the foci of an indexed optic, using an initial index value.
--
ixlistsFrom :: AIxfold (Endo [(i, a)]) i s a -> i -> s -> [(i, a)]
ixlistsFrom o i = ixfoldsrFrom o (\i a -> ((i,a):)) i []
{-# INLINE ixlistsFrom #-}

-- | Collect an applicative over the foci of an indexed optic.
--
ixtraverses_ :: Monoid i => Applicative f => AIxfold (Endo (f ())) i s a -> (i -> a -> f r) -> s -> f ()
ixtraverses_ p f = ixfoldsr p (\i a fu -> void (f i a) *> fu) (pure ())
{-# INLINE ixtraverses_ #-}

-- | Concatenate the results of a function of the foci of an indexed optic.
--
-- @
-- 'concats' o ≡ 'ixconcats' o '.' 'const'
-- @
--
-- >>> ixconcats ixtraversed (\i x -> [i + x, i + x + 1]) [1,2,3,4]
-- [1,2,3,4,5,6,7,8]
--
ixconcats :: Monoid i => AIxfold [r] i s a -> (i -> a -> [r]) -> s -> [r]
ixconcats o f = ixfoldMapOf o f mempty
{-# INLINE ixconcats #-}

-- | Find the first focus of an indexed optic that satisfies a predicate, if one exists.
--
ixfinds :: Monoid i => AIxfold (Endo (Maybe (i, a))) i s a -> (i -> a -> Bool) -> s -> Maybe (i, a)
ixfinds o f = ixfoldsr o (\i a y -> if f i a then Just (i,a) else y) Nothing
{-# INLINE ixfinds #-}

------------------------------------------------------------------------------
-- Auxilliary Types
------------------------------------------------------------------------------

type All = Prod Bool

type Any = Bool

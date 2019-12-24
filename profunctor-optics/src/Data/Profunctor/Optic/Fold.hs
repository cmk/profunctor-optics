{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module Data.Profunctor.Optic.Fold (
    -- * Fold & Ixfold
    Fold
  , Ixfold
  , fold_
  , folding 
  , foldVl
  , ifoldVl
  , afold
  , aifold
    -- * Fold1 & Ixfold1
  , Fold1
  , Ixfold1
  , fold1_
  , folding1
  , fold1Vl
  , ifold1Vl
  , afold1
  , aifold1
    -- * Optics
  , folded
  , folded_
  , folded1 
  , folded1_
  , unital
  , nonunital
  , presemiring
  , summed
  , summed1
  , multiplied
  , multiplied1
    -- * Indexed optics
  , ifolded
  , ifoldedRep
  , ifolded1
  , aifolded
  , aifolded1
    -- * Primitive operators
  , withFold
  , withIxfold
  , withFold1
  , withIxfold1
    -- * Operators
  , lists
  , (^..)
  , ilists
  , ilistsFrom
  , (^%%)
  , nelists
  , folds
  , ifolds
  , folds1
  , foldsa
  , foldsp
  , folds1p
  , foldsr
  , ifoldsr
  , ifoldsrFrom
  , foldsl
  , ifoldsl
  , ifoldslFrom
  , foldsr'
  , ifoldsr'
  , foldsl'
  , ifoldsl'
  , foldsrM
  , ifoldsrM
  , foldslM
  , ifoldslM
  , traverses_
  , itraverses_
    -- * Auxilliary Types
  , All, Any
  , Nedl(..)
) where

import Control.Monad (void)
import Control.Monad.Reader as Reader hiding (lift)
import Data.Bool.Instance () -- Semigroup / Monoid / Semiring instances
import Data.Foldable (Foldable, foldMap, traverse_)
import Data.Key as K
import Data.Monoid hiding (All(..), Any(..))
import Data.Profunctor.Optic.Carrier
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Traversal
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.View
import Data.Semiring (Semiring(..), Prod(..))

import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Functor.Rep as F
import qualified Data.Semiring as Rng
import qualified Data.List.NonEmpty as NEL

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> :set -XRankNTypes
-- >>> import Control.Exception hiding (catches)
-- >>> import Data.Functor.Identity
-- >>> import Data.List.Index as LI
-- >>> import Data.Int.Instance ()
-- >>> import Data.List.NonEmpty (NonEmpty(..))
-- >>> import qualified Data.List.NonEmpty as NE
-- >>> import Data.Map.NonEmpty as Map1
-- >>> import Data.Map as Map
-- >>> import Data.Maybe
-- >>> import Data.Monoid
-- >>> import Data.Semiring hiding (unital,nonunital,presemiring)
-- >>> :load Data.Profunctor.Optic
-- >>> let itraversed :: Ixtraversal Int [a] [b] a b ; itraversed = itraversalVl itraverse
-- >>> let iat :: Int -> Ixaffine' Int [a] a; iat i = iaffine' (\s -> flip LI.ifind s $ \n _ -> n==i) (\s a -> LI.modifyAt i (const a) s) 

---------------------------------------------------------------------
-- 'Fold' & 'Ixfold'
---------------------------------------------------------------------

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
-- This can be useful to lift operations from @Data.List@ and elsewhere into a 'Fold'.
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
foldVl f = coercer . traversalVl f . coercer
{-# INLINE foldVl #-}

-- | Obtain a 'Ixfold' from a Van Laarhoven 'Fold'.
--
ifoldVl :: (forall f. Applicative f => (i -> a -> f b) -> s -> f t) -> Ixfold i s a
ifoldVl f = coercer . itraversalVl f . coercer
{-# INLINE ifoldVl #-}

-- | TODO: Document
--
-- @
-- afold :: Monoid r => ((a -> r) -> s -> r) -> AFold r s a
-- @
--
afold :: Monoid r => ((a -> r) -> s -> r) -> APrimView r s t a b
afold f = Star #. (Const #.) #. f .# (getConst #.) .# runStar
{-# INLINE afold #-}

-- | TODO: Document
--
aifold :: Monoid r => ((i -> a -> r) -> s -> r) -> AIxfold r i s a
aifold f = afold $ \iar s -> f (curry iar) $ snd s
{-# INLINE aifold #-}

---------------------------------------------------------------------
-- 'Fold1' & 'Ixfold1'
---------------------------------------------------------------------

-- | Obtain a 'Fold1' directly.
--
-- @ 
-- 'fold1_' ('nelists' o) ≡ o
-- 'fold1_' f ≡ 'to' f . 'fold1Vl' 'traverse1_'
-- 'fold1_' f ≡ 'coercer' . 'lmap' f . 'lift' 'traverse1_'
-- @
--
-- See 'Data.Profunctor.Optic.Property'.
--
-- This can be useful to repn operations from @Data.List.NonEmpty@ and elsewhere into a 'Fold1'.
--
fold1_ :: Foldable1 f => (s -> f a) -> Fold1 s a
fold1_ f = to f . fold1Vl traverse1_
{-# INLINE fold1_ #-}

-- | Obtain a 'Fold1' from a 'Traversable1' functor.
--
-- @
-- 'folding1' f ≡ 'traversed1' . 'to' f
-- 'folding1' f ≡ 'fold1Vl' 'traverse1' . 'to' f
-- @
--
folding1 :: Traversable1 f => (s -> a) -> Fold1 (f s) a
folding1 f = fold1Vl traverse1 . to f
{-# INLINE folding1 #-}

-- | Obtain a 'Fold1' from a Van Laarhoven 'Fold1'.
--
-- See 'Data.Profunctor.Optic.Property'.
--
fold1Vl :: (forall f. Apply f => (a -> f b) -> s -> f t) -> Fold1 s a
fold1Vl f = coercer . repn f . coercer
{-# INLINE fold1Vl #-}

-- | Obtain a 'Ixfold1' from a Van Laarhoven 'Fold1'.
--
ifold1Vl :: (forall f. Apply f => (i -> a -> f b) -> s -> f t) -> Ixfold1 i s a
ifold1Vl f = coercer . itraversal1Vl f . coercer
{-# INLINE ifold1Vl #-}

-- | TODO: Document
--
-- @
-- afold1 :: Semigroup r => ((a -> r) -> s -> r) -> AFold1 r s a
-- @
--
afold1 :: Semigroup r => ((a -> r) -> s -> r) -> APrimView r s t a b
afold1 f = Star #. (Const #.) #. f .# (getConst #.) .# runStar
{-# INLINE afold1 #-}

-- | TODO: Document
--
aifold1 :: Semigroup r => ((i -> a -> r) -> s -> r) -> AIxfold1 r i s a
aifold1 f = afold1 $ \iar s -> f (curry iar) $ snd s
{-# INLINE aifold1 #-}

---------------------------------------------------------------------
-- Optics 
---------------------------------------------------------------------

-- | Obtain a 'Fold' from a 'Traversable' functor.
--
folded :: Traversable f => Fold (f a) a
folded = folding id
{-# INLINE folded #-}

-- | The canonical 'Fold'.
--
-- @
-- 'Data.Foldable.foldMap' ≡ 'withFold' 'folded_''
-- @
--
folded_ :: Foldable f => Fold (f a) a
folded_ = fold_ id
{-# INLINE folded_ #-}

-- | Obtain a 'Fold1' from a 'Traversable1' functor.
--
folded1 :: Traversable1 f => Fold1 (f a) a
folded1 = folding1 id
{-# INLINE folded1 #-}

-- | The canonical 'Fold1'.
--
-- @
-- 'Data.Semigroup.Foldable.foldMap1' ≡ 'withFold1' 'folded1_''
-- @
--
folded1_ :: Foldable1 f => Fold1 (f a) a
folded1_ = fold1_ id
{-# INLINE folded1_ #-}

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

-- | Expression in a semiring expression with no multiplicative unit.
--
-- @ 
-- 'nonunital' ≡ 'summed' . 'multiplied1'
-- @
--
-- >>> folds1 nonunital $ (fmap . fmap) Just [1 :| [2], 3 :| [4 :: Int]]
-- Just 14
--
nonunital :: Foldable f => Foldable1 g => Monoid r => Semiring r => AFold r (f (g a)) a
nonunital = summed . multiplied1
{-# INLINE nonunital #-}

-- | Expression in a semiring with no additive or multiplicative unit.
--
-- @ 
-- 'presemiring' ≡ 'summed1' . 'multiplied1'
-- @
--
presemiring :: Foldable1 f => Foldable1 g => Semiring r => AFold1 r (f (g a)) a
presemiring = summed1 . multiplied1
{-# INLINE presemiring #-}

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

-- | Semigroup sum of a non-empty foldable collection.
--
-- >>> 1 <> 2 <> 3 <> 4 :: Int
-- 10
-- >>> folds1 summed1 $ 1 :| [2,3,4 :: Int]
-- 10
--
summed1 :: Foldable1 f => Semigroup r => AFold1 r (f a) a
summed1 = afold1 foldMap1
{-# INLINE summed1 #-}

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

-- | Semiring product of a non-empty foldable collection. 
--
-- >>> folds1 multiplied1 $ fmap Just (1 :| [2..(5 :: Int)])
-- Just 120 
--
multiplied1 :: Foldable1 f => Semiring r => AFold1 r (f a) a
multiplied1 = afold1 Rng.product1
{-# INLINE multiplied1 #-}

---------------------------------------------------------------------
-- Indexed optics 
---------------------------------------------------------------------

-- | Obtain an 'AIxfold' from a 'FoldableWithKey'.
--
-- @
-- f '^%%' 'ifolded' ≡ 'toKeyedList' f
-- @
--
ifolded :: FoldableWithKey f => Ixfold (Key f) (f a) a
ifolded = ifoldVl K.traverseWithKey_
{-# INLINE ifolded #-}

-- | Obtain an 'Ixfold' from a 'F.Representable' functor.
--
ifoldedRep :: F.Representable f => Traversable f => Ixfold (F.Rep f) (f a) a
ifoldedRep = ifoldVl F.itraverseRep
{-# INLINE ifoldedRep #-}

-- | Obtain an 'Ixfold1' from a 'FoldableWithKey1'.
--
ifolded1 :: FoldableWithKey1 f => Ixfold1 (Key f) (f a) a
ifolded1 = ifold1Vl K.traverseWithKey1_
{-# INLINE ifolded1 #-}

-- | Obtain an 'AIxfold' from a 'FoldableWithKey'.
--
aifolded :: FoldableWithKey f => Monoid r => AIxfold r (Key f) (f a) a
aifolded = aifold K.foldMapWithKey
{-# INLINE aifolded #-}

-- | Obtain an 'AIxfold1' from a 'FoldableWithKey1'.
--
aifolded1 :: FoldableWithKey1 f => Semigroup r => AIxfold1 r (Key f) (f a) a
aifolded1 = aifold1 K.foldMapWithKey1
{-# INLINE aifolded1 #-}

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

-- | Map an optic to a monoid and combine the results.
--
-- @
-- 'Data.Foldable.foldMap' = 'withFold' 'folded_''
-- @
--
-- >>> withFold both id (["foo"], ["bar", "baz"])
-- ["foo","bar","baz"]
--
-- >>> :t withFold traversed
-- withFold traversed
--   :: (Monoid r, Traversable f) => (a -> r) -> f a -> r
--
-- @
-- 'withFold' :: 'Monoid' r => 'AFold' r s a -> (a -> r) -> s -> r
-- @
--
withFold :: Monoid r => APrimView r s t a b -> (a -> r) -> s -> r
withFold = withPrimView
{-# INLINE withFold #-}

-- | Map an indexed optic to a monoid and combine the results.
--
-- Note that most indexed optics do not use their output index:
--
-- >>> withIxfold itraversed const 100 [1..5]
-- 10
-- >>> withIxfold itraversed const 100 []
-- 0
--
withIxfold :: Monoid r => AIxfold r i s a -> (i -> a -> r) -> i -> s -> r
withIxfold o f = curry $ withFold o (uncurry f)
{-# INLINE withIxfold #-}

-- | Map an optic to a semigroup and combine the results.
--
-- @
-- 'withFold1' :: 'Semigroup' r => 'AFold1' r s a -> (a -> r) -> s -> r
-- @
--
withFold1 :: Semigroup r => APrimView r s t a b -> (a -> r) -> s -> r
withFold1 = withPrimView
{-# INLINE withFold1 #-}

-- | Map an indexed optic to a semigroup and combine the results.
--
-- >>> :t flip withIxfold1 Map.singleton
-- flip withIxfold1 Map.singleton
--   :: Ord i => AIxfold1 (Map i a) i s a -> i -> s -> Map i a
--
-- @
-- 'withIxfold1' :: 'Semigroup' r => 'AIxfold1' r s a -> (i -> a -> r) -> i -> s -> r
-- @
--
withIxfold1 :: Semigroup r => AIxfold1 r i s a -> (i -> a -> r) -> i -> s -> r
withIxfold1 o f = curry $ withFold1 o (uncurry f)
{-# INLINE withIxfold1 #-}

---------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------

-- | Collect the foci of an optic into a list.
--
lists :: AFold (Endo [a]) s a -> s -> [a]
lists o = foldsr o (:) []
{-# INLINE lists #-}

infixl 8 ^..

-- | Infix alias of 'lists'.
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

-- | Collect the foci of an indexed optic into a list of index-value pairs.
--
-- This is only for use with the few indexed optics that don't ignore their 
-- output index. You most likely want to use 'ilists'.
--
ilistsFrom :: AIxfold (Endo [(i, a)]) i s a -> i -> s -> [(i, a)]
ilistsFrom o i = ifoldsrFrom o (\i a -> ((i,a):)) i []
{-# INLINE ilistsFrom #-}

-- | Collect the foci of an indexed optic into a list of index-value pairs.
--
-- @
-- 'lists' l ≡ 'map' 'snd' '.' 'ilists' l
-- @
--
ilists :: Monoid i => AIxfold (Endo [(i, a)]) i s a -> s -> [(i, a)]
ilists o = ifoldsr o (\i a -> ((i,a):)) []
{-# INLINE ilists #-}

infixl 8 ^%%

-- | Infix version of 'ilists'.
--
(^%%) :: Monoid i => s -> AIxfold (Endo [(i, a)]) i s a -> [(i, a)]
(^%%) = flip ilists
{-# INLINE (^%%) #-}

-- | Extract a 'NonEmpty' of the foci of an optic.
--
-- >>> nelists bitraversed1 ('h' :| "ello", 'w' :| "orld")
-- ('h' :| "ello") :| ['w' :| "orld"]
--
nelists :: AFold1 (Nedl a) s a -> s -> NonEmpty a
nelists l = flip getNedl [] . withFold1 l (Nedl #. (:|))
{-# INLINE nelists #-}

-- | TODO: Document
--
folds :: Monoid a => AFold a s a -> s -> a
folds = flip withFold id
{-# INLINE folds #-}

-- | TODO: Document
--
ifolds :: Monoid i => Monoid a => AIxfold (i, a) i s a -> s -> (i, a)
ifolds o = withIxfold o (,) mempty
{-# INLINE ifolds #-}

-- | TODO: Document
--
folds1 :: Semigroup a => AFold1 a s a -> s -> a
folds1 = flip withFold1 id
{-# INLINE folds1 #-}

-- | TODO: Document
-- 
-- @
-- foldsa :: Fold s a -> s -> [a]
-- foldsa :: Applicative f => Setter s t a b -> s -> f a
-- @
--
foldsa :: Applicative f => Monoid (f a) => AFold (f a) s a -> s -> f a
foldsa = flip withFold pure
{-# INLINE foldsa #-}

-- | Compute the semiring product of the foci of an optic.
--
-- For semirings without a multiplicative unit this is equivalent to @const mempty@:
--
-- >>> foldsp folded Just [1..(5 :: Int)]
-- Just 0
--
-- In this situation you most likely want to use 'folds1p'.
--
foldsp :: Monoid r => Semiring r => AFold (Prod r) s a -> (a -> r) -> s -> r
foldsp o p = getProd . withFold o (Prod . p)
{-# INLINE foldsp #-}

-- | Compute the semiring product of the foci of an optic.
--
folds1p :: Semiring r => AFold (Prod r) s a -> (a -> r) -> s -> r
folds1p o p = getProd . withFold1 o (Prod . p)
{-# INLINE folds1p #-}

-- | Right fold over an optic.
--
-- >>> foldsr folded (<>) 0 [1..5::Int]
-- 15
--
foldsr :: AFold (Endo r) s a -> (a -> r -> r) -> r -> s -> r
foldsr o f r = (`appEndo` r) . withFold o (Endo . f)
{-# INLINE foldsr #-}

-- | Indexed right fold over an indexed optic.
--
-- @
-- 'foldsr' o ≡ 'ifoldsr' o '.' 'const'
-- 'foldrWithKey' f ≡ 'ifoldsr' 'ifolded' f
-- @
--
-- >>> ifoldsr itraversed (\i a -> ((show i ++ ":" ++ show a ++ ", ") ++)) [] [1,3,5,7,9]
-- "0:1, 1:3, 2:5, 3:7, 4:9, "
--
ifoldsr :: Monoid i => AIxfold (Endo r) i s a -> (i -> a -> r -> r) -> r -> s -> r
ifoldsr o f = ifoldsrFrom o f mempty
{-# INLINE ifoldsr #-}

-- | Indexed right fold over an indexed optic, using an initial index value.
--
-- This is only for use with the few indexed optics that don't ignore their 
-- output index. You most likely want to use 'ifoldsr'.
--
ifoldsrFrom :: AIxfold (Endo r) i s a -> (i -> a -> r -> r) -> i -> r -> s -> r
ifoldsrFrom o f i r = (`appEndo` r) . withIxfold o (\j -> Endo . f j) i
{-# INLINE ifoldsrFrom #-}

-- | Left fold over an optic.
--
foldsl :: AFold (Dual (Endo r)) s a -> (r -> a -> r) -> r -> s -> r
foldsl o f r = (`appEndo` r) . getDual . withFold o (Dual . Endo . flip f)
{-# INLINE foldsl #-}

-- | Left fold over an indexed optic.
--
-- @
-- 'foldsl' o ≡ 'ifoldsl' o '.' 'const'
-- 'foldlWithKey' f ≡ 'ifoldsl' 'ifolded' f
-- @
--
ifoldsl :: Monoid i => AIxfold (Dual (Endo r)) i s a -> (i -> r -> a -> r) -> r -> s -> r
ifoldsl o f = ifoldslFrom o f mempty
{-# INLINE ifoldsl #-}

-- | Left fold over an indexed optic, using an initial index value.
--
-- This is only for use with the few indexed optics that don't ignore their 
-- output index. You most likely want to use 'ifoldsl'.
--
ifoldslFrom :: AIxfold (Dual (Endo r)) i s a -> (i -> r -> a -> r) -> i -> r -> s -> r
ifoldslFrom o f i r = (`appEndo` r) . getDual . withIxfold o (\i -> Dual . Endo . flip (f i)) i
{-# INLINE ifoldslFrom #-}

-- | Strict right fold over an optic.
--
foldsr' :: AFold (Dual (Endo (Endo r))) s a -> (a -> r -> r) -> r -> s -> r
foldsr' l f z0 xs = foldsl l f' (Endo id) xs `appEndo` z0 where f' (Endo k) x = Endo $ \ z -> k $! f x z
{-# INLINE foldsr' #-}

-- | Strict right fold over an indexed optic.
--
-- @
-- 'foldsr'' o ≡ 'ifoldsr'' o '.' 'const'
-- 'foldrWithKey'' f ≡ 'ifoldsr'' 'ifolded' f
-- @
--
ifoldsr' :: Monoid i => AIxfold (Dual (Endo (r -> r))) i s a -> (i -> a -> r -> r) -> r -> s -> r
ifoldsr' l f z0 xs = ifoldsl l f' id xs z0 where f' i k x z = k $! f i x z
{-# INLINE ifoldsr' #-}

-- | Strict left fold over an optic.
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
-- 'foldsl'' :: 'Affine'' s a -> (c -> a -> c) -> c -> s -> c
-- @
--
foldsl' :: AFold (Endo (Endo r)) s a -> (r -> a -> r) -> r -> s -> r
foldsl' o f r s = foldsr o f' (Endo id) s `appEndo` r where f' x (Endo k) = Endo $ \z -> k $! f z x
{-# INLINE foldsl' #-}

-- | Strict left fold over an indexed optic.
--
-- @
-- 'foldsl'' o ≡ 'ifoldsl'' o '.' 'const'
-- 'foldlWithKey'' f ≡ 'ifoldsl'' 'ifolded' f
-- @
--
ifoldsl' :: Monoid i => AIxfold (Endo (r -> r)) i s a -> (i -> r -> a -> r) -> r -> s -> r
ifoldsl' l f z0 xs = ifoldsr l f' id xs z0 where f' i x k z = k $! f i z x
{-# INLINE ifoldsl' #-}

-- | Monadic right fold over an optic.
--
foldsrM :: Monad m => AFold (Dual (Endo (r -> m r))) s a -> (a -> r -> m r) -> r -> s -> m r
foldsrM l f z0 xs = foldsl l f' return xs z0 where f' k x z = f x z >>= k
{-# INLINE foldsrM #-}

-- | Monadic right fold over an indexed optic.
--
-- @
-- 'foldsrM' ≡ 'ifoldrM' '.' 'const'
-- @
--
ifoldsrM :: Monoid i => Monad m => AIxfold (Dual (Endo (r -> m r))) i s a -> (i -> a -> r -> m r) -> r -> s -> m r
ifoldsrM o f z0 xs = ifoldsl o f' return xs z0 where f' i k x z = f i x z >>= k
{-# INLINE ifoldsrM #-}

-- | Monadic left fold over an optic.
--
foldslM :: Monad m => AFold (Endo (r -> m r)) s a -> (r -> a -> m r) -> r -> s -> m r
foldslM o f z0 xs = foldsr o f' return xs z0 where f' x k z = f z x >>= k
{-# INLINE foldslM #-}

-- | Monadic left fold over an indexed optic.
--
-- @
-- 'foldslM' ≡ 'ifoldslM' '.' 'const'
-- @
--
ifoldslM :: Monoid i => Monad m => AIxfold (Endo (r -> m r)) i s a -> (i -> r -> a -> m r) -> r -> s -> m r
ifoldslM o f z0 xs = ifoldsr o f' return xs z0 where f' i x k z = f i z x >>= k
{-# INLINE ifoldslM #-}

-- | Applicative fold over an optic.
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

-- | Applicative fold over an indexed optic.
--
itraverses_ :: Monoid i => Applicative f => AIxfold (Endo (f ())) i s a -> (i -> a -> f r) -> s -> f ()
itraverses_ p f = ifoldsr p (\i a fu -> void (f i a) *> fu) (pure ())
{-# INLINE itraverses_ #-}

------------------------------------------------------------------------------
-- Auxilliary Types
------------------------------------------------------------------------------

type All = Prod Bool

type Any = Bool

-- A non-empty difference list.
newtype Nedl a = Nedl { getNedl :: [a] -> NEL.NonEmpty a }

instance Semigroup (Nedl a) where
  Nedl f <> Nedl g = Nedl (f . NEL.toList . g)

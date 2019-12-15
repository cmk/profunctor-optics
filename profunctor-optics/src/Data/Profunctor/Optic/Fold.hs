{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
module Data.Profunctor.Optic.Fold where
{- (
    -- * Fold & Ixfold
    Fold
  , Ixfold
  , fold_
  , folding 
  , foldVl
  , ifoldVl
  , toFold
  , cloneFold
    -- * Optics
  , folded
  , folded_
  , ifoldedRep
  , unital
  , summed
  , multiplied
    -- * Primitive operators
  , withFold
  , withIxfold
    -- * Operators
  , lists
  , (^..)
  , ilists
  , ilistsFrom
  , (^%%)
  , folds
  , foldsa
  , foldsp
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
    -- * Carriers
  , FoldRep
  , AFold
  , AIxfold
  , afold
  , aifold
  , acofold
) where
-}
import Control.Monad (void)
import Control.Monad.Reader as Reader hiding (lift)
import Data.Bool.Instance () -- Semigroup / Monoid / Semiring instances
import Data.Foldable (Foldable, foldMap, traverse_)
import Data.Monoid hiding (All(..), Any(..))
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Traversal (traversalVl, itraversalVl)
import Data.Profunctor.Optic.Types
import Data.Profunctor.Optic.View
import Data.Semiring (Semiring(..), Prod(..))

import qualified Data.Functor.Rep as F
import qualified Data.Semiring as Rng

import Data.Functor.Foldable as F

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> :set -XRankNTypes
-- >>> import Control.Exception hiding (catches)
-- >>> import Data.Functor.Identity
-- >>> import Data.List.Index as LI
-- >>> import Data.Int.Instance ()
-- >>> import Data.Map as Map
-- >>> import Data.Maybe
-- >>> import Data.Monoid
-- >>> import Data.Semiring hiding (unital,nonunital,presemiring)
-- >>> :load Data.Profunctor.Optic
-- >>> let itraversed :: Ixtraversal Int [a] [b] a b ; itraversed = itraversalVl itraverse
-- >>> let iat :: Int -> Ixtraversal0' Int [a] a; iat i = itraversal0' (\s -> flip LI.ifind s $ \n _ -> n==i) (\s a -> LI.modifyAt i (const a) s) 

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

-- | Obtain a 'Fold' from a Van Laarhoven 'Fold'.
--
ifoldVl :: (forall f. Applicative f => (i -> a -> f b) -> s -> f t) -> Ixfold i s a
ifoldVl f = coercer . itraversalVl f . coercer
{-# INLINE ifoldVl #-}

-- | Obtain a 'Fold' from a 'View' or 'AFold'.
--
toFold :: AView s a -> Fold s a
toFold = to . view
{-# INLINE toFold #-}

-- | Obtain a 'Fold' from a 'AFold'.
--
cloneFold :: Monoid a => AFold a s a -> View s a
cloneFold = cloneView
{-# INLINE cloneFold #-}

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

-- | Obtain an 'Ixfold' from a 'F.Representable' functor.
--
ifoldedRep :: F.Representable f => Traversable f => Ixfold (F.Rep f) (f a) a
ifoldedRep = ifoldVl F.itraverseRep
{-# INLINE ifoldedRep #-}

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
-- >>> :t withFold . fold_
-- withFold . fold_
--   :: (Monoid r, Foldable f) => (s -> f a) -> (a -> r) -> s -> r
--
-- >>> :t withFold traversed
-- withFold traversed
--   :: (Monoid r, Traversable f) => (a -> r) -> f a -> r
--
withFold :: Monoid r => AFold r s a -> (a -> r) -> s -> r
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
withIxfold o f = curry $ withPrimView o (uncurry f)
{-# INLINE withIxfold #-}

---------------------------------------------------------------------
-- Operators
-------------------------------------------------------------------------------

-- | Collect the foci of an optic into a list.
--
lists :: AFold (Endo [a]) s a -> s -> [a]
lists o = foldsr o (:) []
{-# INLINE lists #-}

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

-- | TODO: Document
--
folds :: Monoid a => AFold a s a -> s -> a
folds = flip withFold id
{-# INLINE folds #-}

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
-- 'foldsl'' :: 'Traversal0'' s a -> (c -> a -> c) -> c -> s -> c
-- @
--
foldsl' :: AFold (Endo (Endo r)) s a -> (r -> a -> r) -> r -> s -> r
foldsl' o f r s = foldsr o f' (Endo id) s `appEndo` r where f' x (Endo k) = Endo $ \z -> k $! f z x
{-# INLINE foldsl' #-}

-- | Strict left fold over an indexed optic.
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

---------------------------------------------------------------------
-- Carriers
---------------------------------------------------------------------

type FoldRep r = Star (Const r)

type AFold r s a = Optic' (FoldRep r) s a
--type AFold s a = forall r. Monoid r => Optic' (FoldRep r) s a

type AIxfold r i s a = IndexedOptic' (FoldRep r) i s a

type CofoldRep r = Costar (Const r)

-- | TODO: Document
--
-- @
-- afold :: ((a -> r) -> s -> r) -> AFold r s a
-- @
--
afold :: ((a -> r) -> s -> r) -> Optic (FoldRep r) s t a b
afold arsr = Star #. (Const #.) #. arsr .# (getConst #.) .# runStar
{-# INLINE afold #-}

-- | TODO: Document
--
aifold :: ((i -> a -> r) -> s -> r) -> AIxfold r i s a
aifold f = afold $ \iar s -> f (curry iar) $ snd s
{-# INLINE aifold #-}

-- | TODO: Document
--
acofold :: ((r -> b) -> r -> t) -> Optic (CofoldRep r) s t a b 
acofold o = Costar #. (.# getConst) #. o .#  (.# Const) .# runCostar  
{-# INLINE acofold #-}

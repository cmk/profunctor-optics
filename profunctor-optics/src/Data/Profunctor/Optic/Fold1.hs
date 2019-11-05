module Data.Profunctor.Optic.Fold.NonEmpty where

import Data.DList.NonEmpty (NonEmptyDList)
import Data.Functor.Apply (Apply(..))
import Data.List.NonEmpty (NonEmpty(..))
import Data.Profunctor.Optic.View (view, to)
import Data.Profunctor.Optic.Prelude
import Data.Profunctor.Optic.Type
import Data.Semigroup
import Data.Semigroup.Foldable
import Data.Semigroup.Traversable
import qualified Data.DList.NonEmpty as NEL

---------------------------------------------------------------------
-- 'Fold1'
---------------------------------------------------------------------

{-
A 'Fold1' can interpret 'a' in a semigroup so long as 's' can also be interpreted that way.
Fold1 laws:
fold1_complete :: Fold1 s a -> Bool
fold1_complete o = tripping o $ folding1 (toNonEmptyOf o)
-}

-- | Obtain a 'Fold' by lifting an operation that returns a 'Foldable' result.
--
-- This can be useful to lift operations from @Data.List@ and elsewhere into a 'Fold'.
--
-- >>> [1,2,3,4] ^.. folding tail
-- [2,3,4]
--
folding1 :: Foldable1 f => (s -> f a) -> Fold1 s a
folding1 f = coercer . lmap f . lift traverse1_
{-# INLINE folding1 #-}

folded1 :: Traversable1 f => (s -> a) -> Fold1 (f s) a
folded1 f = lift traverse1 . to f

fold1Like :: Semigroup r => ((a -> r) -> s -> r) -> AFold1 r s a
fold1Like = between ((Star . (Const . ))) ((getConst .) . runStar)

fold1Like' :: Foldable1 f => AFold1 r (f a) a
fold1Like' = fold1Like foldMap1

cloneFold1 :: Semigroup a => AFold1 a s a -> Fold1 s a
cloneFold1 = to . view

-- | Transform a Van Laarhoven 'Fold1' into a profunctor 'Fold1'.
--
fold1VL :: (forall f. Apply f => (a -> f b) -> s -> f t) -> Fold1 s a
fold1VL f = coercer . lift f . coercer
{-# INLINE fold1VL #-}

-- | Obtain a 'Fold' using a 'Traversable' functor.
--
-- @
-- 'folded' f ≡ 'lift' 'traverse' . 'to' f
-- @
--
folded1 :: Traversable1 f => (s -> a) -> Fold1 (f s) a
folded1 f = traversed1 . to f
{-# INLINE folded1 #-}

-- | Obtain a 'Fold1' by lifting an operation that returns a 'Foldable1' result.
--
-- @ 
-- 'folding1' ('toNonEmptyOf' o) ≡ o
-- @
--
-- This can be useful to lift operations from @Data.NonEmpty@ and elsewhere into a 'Fold1'.
--
-- >>> [1,2,3,4] ^.. folding1 tail
-- [2,3,4]
--
--
-- See 'Data.Profunctor.Optic.Property'.
--
folding1 :: Foldable1 f => (s -> f a) -> Fold1 s a
folding1 f = coercer . lmap f . lift traverse_
{-# INLINE folding1 #-}

-- | TODO: Document
--
folding1' :: Foldable1 f => Fold1 (f a) a
folding1' = folding1 id
{-# INLINE folding1' #-}

-- | Build a 'Fold1' from a 'View'.
--
toFold1 :: AView s a -> Fold1 s a
toFold1 = to . view
{-# INLINE toFold1 #-}

-- | Build a monoidal 'View' from a 'Fold'.
--
fromFold1 :: Semigroup a => AFold1 a s a -> View s a
fromFold1 = cloneView
{-# INLINE fromFold1 #-}

---------------------------------------------------------------------
-- 'Fold1Rep'
---------------------------------------------------------------------

-- | TODO: Document
--
afold1 :: Semigroup r => ((a -> r) -> s -> r) -> AFold1 r s a
afold1 = between (Star . (Const .)) ((getConst .) . runStar)

-- | TODO: Document
--
afold1' :: Foldable f => AFold1 r (f a) a
afold1' = afold1 foldMap

-- | TODO: Document
--
recursing1 :: Recursive s => AFold1 a s (Base s a)
recursing1 = afold1 F.fold

---------------------------------------------------------------------
-- Primitive operators
---------------------------------------------------------------------

foldMap1Of :: Semigroup r => AFold1 r s a -> (a -> r) -> s -> r
foldMap1Of = between ((getConst .) . runStar) ((Star . (Const . )))

-- | Extract a 'NonEmpty' of the targets of 'Fold1'.
--
-- >>> toNonEmptyOf both1 ("hello", "world")
-- "hello" :| ["world"]
--
-- @
-- 'toNonEmptyOf' :: 'View' s a        -> s -> NonEmpty a
-- 'toNonEmptyOf' :: 'Fold1' s a       -> s -> NonEmpty a
-- 'toNonEmptyOf' :: 'Lens'' s a       -> s -> NonEmpty a
-- 'toNonEmptyOf' :: 'Iso'' s a        -> s -> NonEmpty a
-- 'toNonEmptyOf' :: 'Traversal1'' s a -> s -> NonEmpty a
-- 'toNonEmptyOf' :: 'Prism'' s a      -> s -> NonEmpty a
-- @
toNonEmptyOf :: AFold1 (NonEmptyDList a) s a -> s -> NonEmpty a
toNonEmptyOf o = flip NEL.apply [] . foldMap1Of o NEL.singleton

-- | Find the join of a sublattice. 
--
join1 :: Lattice a => AFold1 (Endo (Endo a)) s a -> s -> a
join1 o = undefined

-- | Find the meet of a sublattice.
--
meet1 :: Lattice a => AFold1 (Endo (Endo a)) s a -> s -> a
meet1 o = undefined

nonunital :: Foldable f => Foldable g => Semiring r => AFold1 r (f (g a)) a
nonunital = afold Rng.nonunital -- ???

presemiring :: Foldable1 f => Foldable1 g => Semiring r => AFold1 r (f (g a)) a
presemiring = afold1 Rng.presemiring

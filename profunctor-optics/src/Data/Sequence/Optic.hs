{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
-- | Left and right carriers are characterized by their representation
-- functors ('Rep' and 'Corep'). 'Iso' sits at the top where both
-- are trivial ('Identity'). 'Adjoint' sits at the bottom where they
-- form a full adjunction (@'Corep' p ⊣ 'Rep' p@). A left-indexed
-- ('Ix') optic threads an index through the left adjoint functor
-- @(,) k@, while a right-indexed ('Cx') optic threads a coindex
-- through the right adjoint functor @(->) k@.
module Data.Sequence.Optic (
    -- * Types
    Seq
    -- * Iso
  , reversed
  , viewedl
  , viewedr
    -- * Prism
  , consed
  , snoced
    -- * Traversal0
  , at
  , ixat
  , found
    -- * Traversal
  , traversed
  , ixtraversed
  , slicedTo
  , slicedFrom
  , sliced
    -- * Fold0
  , headed
  , lasted
  , foundIndex
  , foundIndexR
    -- * Fold
  , folded
  , ixfolded
    -- * Setter
  , ixmapped
  , adjusted
  , updated
  , sorted
  , ixfiltered
    -- * Adjoint
  , filtered
    -- * Dual Optics
    -- ** Cxlens
  , zipped
    -- ** Cotraversal
  , zippedTraverse
    -- ** Cxsetter
  , cxmapped
  , cxfiltered
    -- ** Cxtraversal
  , cxtraversed
    -- ** Cxfold
  , cxfolded
) where

import Data.Profunctor.Optic hiding (zipped, filtered)
import Data.Profunctor.Optic.Import
import Data.Maybe (fromMaybe)
import Data.Sequence (Seq, ViewL(..), ViewR(..), viewl, viewr)
import qualified Data.Sequence as Seq
import qualified Data.Foldable as Foldable
import Prelude

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> import Data.Sequence (fromList)
-- >>> import Data.Profunctor.Optic
-- >>> import qualified Data.Sequence as Seq

---------------------------------------------------------------------
-- Iso
---------------------------------------------------------------------

-- | 'Seq' is reversible.
reversed :: Iso' (Seq a) (Seq a)
reversed = iso Seq.reverse Seq.reverse
{-# INLINE reversed #-}

---------------------------------------------------------------------
-- Prism
---------------------------------------------------------------------

-- | Prism for cons-cell view of 'Seq'.
consed :: Prism' (Seq a) (a, Seq a)
consed = prism' sa bt
  where
    sa s = case viewl s of EmptyL -> Nothing; a Seq.:< as -> Just (a, as)
    bt (a, as) = a Seq.<| as
{-# INLINE consed #-}

-- | Prism for snoc-cell view of 'Seq'.
snoced :: Prism' (Seq a) (Seq a, a)
snoced = prism' sa bt
  where
    sa s = case viewr s of EmptyR -> Nothing; as Seq.:> a -> Just (as, a)
    bt (as, a) = as Seq.|> a
{-# INLINE snoced #-}

---------------------------------------------------------------------
-- Traversal0
---------------------------------------------------------------------

-- | /O(log(min(i, n-i)))/. Affine traversal into the element at an
-- index of a 'Seq'.
--
at :: Int -> Traversal0' (Seq a) a
at i = traversalVl0 $ \point f s ->
  case Seq.lookup i s of
    Nothing -> point s
    Just a  -> (\b -> Seq.update i b s) <$> f a
{-# INLINE at #-}

-- | /O(log(min(i, n-i)))/. Indexed affine traversal into the element
-- at an index of a 'Seq'.
--
ixat :: Ixtraversal0' (Sum Int) (Seq a) a
ixat = ixtraversalVl0 $ \point f k s ->
  case Seq.lookup (getSum k) s of
    Nothing -> point s
    Just a  -> fmap (\b -> Seq.update (getSum k) b s) (f k a)
{-# INLINE ixat #-}

-- | Affine traversal into the first element matching a predicate.
found :: (a -> Bool) -> Traversal0' (Seq a) a
found p = traversal0' sa sbt
  where
    sa s = case Seq.findIndexL p s of
      Nothing -> Nothing
      Just i  -> Seq.lookup i s
    sbt s a = case Seq.findIndexL p s of
      Nothing -> s
      Just i  -> Seq.update i a s
{-# INLINE found #-}

---------------------------------------------------------------------
-- Fold0
---------------------------------------------------------------------

-- | First element, if non-empty.
headed :: Fold0 (Seq a) a
headed = fold0 (\s -> case viewl s of EmptyL -> Nothing; a Seq.:< _ -> Just a)
{-# INLINE headed #-}

-- | Last element, if non-empty.
lasted :: Fold0 (Seq a) a
lasted = fold0 (\s -> case viewr s of EmptyR -> Nothing; _ Seq.:> a -> Just a)
{-# INLINE lasted #-}

-- | Index of the first element matching a predicate (from left).
foundIndex :: (a -> Bool) -> Fold0 (Seq a) (Sum Int)
foundIndex p = fold0 (fmap Sum . Seq.findIndexL p)
{-# INLINE foundIndex #-}

-- | Index of the first element matching a predicate (from right).
foundIndexR :: (a -> Bool) -> Fold0 (Seq a) (Sum Int)
foundIndexR p = fold0 (fmap Sum . Seq.findIndexR p)
{-# INLINE foundIndexR #-}

---------------------------------------------------------------------
-- Traversal
---------------------------------------------------------------------

-- | /O(n)/. Indexed traversal over the elements of a 'Seq'.
--
ixtraversed :: Ixtraversal (Sum Int) (Seq a) (Seq b) a b
ixtraversed = ixtraversalVl $ \f k ->
  fmap Seq.fromList . traverse (\(i, a) -> f (k <> Sum i) a) . zip [0..] . Foldable.toList
{-# INLINE ixtraversed #-}

---------------------------------------------------------------------
-- Fold
---------------------------------------------------------------------

-- | /O(n)/. Indexed fold over the elements of a 'Seq'.
--
ixfolded :: Ixfold (Sum Int) (Seq a) a
ixfolded = ixfoldVl $ \f k ->
  traverse (\(i, a) -> f (k <> Sum i) a) . zip [0..] . Foldable.toList
{-# INLINE ixfolded #-}

---------------------------------------------------------------------
-- Setter
---------------------------------------------------------------------

-- | /O(n)/. Indexed setter over the elements of a 'Seq'.
--
ixmapped :: Ixsetter (Sum Int) (Seq a) (Seq b) a b
ixmapped = ixsetter $ \f k -> Seq.mapWithIndex (\i -> f (k <> Sum i))
{-# INLINE ixmapped #-}

-- | Adjust a value at the incoming index.
adjusted :: Ixsetter' (Sum Int) (Seq a) a
adjusted = ixsetter $ \f k -> Seq.adjust' (f k) (getSum k)
{-# INLINE adjusted #-}

-- | Update a value at the incoming index.
updated :: Ixsetter (Sum Int) (Seq a) (Seq a) a a
updated = ixsetter $ \f k -> Seq.adjust' (f k) (getSum k)
{-# INLINE updated #-}

-- | Sort elements by a projection.
--
-- @'sets' 'sorted' f = 'Seq.sortOn' f@
sorted :: Ord b => Adjoint (Seq a) (Seq a) a b
sorted = adjoint Seq.sortOn
{-# INLINE sorted #-}

-- | Indexed filter by predicate.
ixfiltered :: Ixsetter (Sum Int) (Seq a) (Seq a) a Bool
ixfiltered = ixsetter $ \f k s ->
  Seq.fromList [a | (i, a) <- zip [0..] (Foldable.toList s), f (k <> Sum i) a]
{-# INLINE ixfiltered #-}

-- | Filter elements by predicate.
filtered :: Adjoint (Seq a) (Seq a) a Bool
filtered = adjoint Seq.filter
{-# INLINE filtered #-}

---------------------------------------------------------------------
-- Dual optics
---------------------------------------------------------------------

-- | 'Cxlens' viewing a 'Seq' as a representable functor of known
-- length. The coindex is the position.
--
-- Stronger than 'cxtraversed' because the known length eliminates
-- the need for 'Choice'.
--
zipped :: Int -> Cxlens (Sum Int) (Seq a) (Seq b) a b
zipped n = cxlensVl $ \fakb k fs ->
  Seq.fromFunction n $ \i ->
    fakb (fmap (`Seq.index` i) fs) (k <> Sum i)
{-# INLINE zipped #-}

-- | Pointwise 'Cotraversal' over the elements of a 'Seq' at a
-- fixed length.
--
zippedTraverse :: Int -> Cotraversal (Seq a) (Seq b) a b
zippedTraverse n = cotraversalVl $ \fab fs ->
  Seq.fromFunction n (\i -> fab (fmap (`Seq.index` i) fs))
{-# INLINE zippedTraverse #-}

---------------------------------------------------------------------
-- Coindexed optics
---------------------------------------------------------------------

-- | /O(n)/. 'Cxsetter' over the elements of a 'Seq'.
--
-- Cx dual of 'ixmapped'. Threads the 'Int' index as coindex.
--
-- @
-- 'cxsets' cxmapped ≡ 'Seq.mapWithIndex'
-- @
--
cxmapped :: Cxsetter (Sum Int) (Seq a) (Seq b) a b
cxmapped = cxsetter $ \f k -> Seq.mapWithIndex (\i -> f (k <> Sum i))
{-# INLINE cxmapped #-}

-- | Coindexed filter over elements with positional coindex.
cxfiltered :: Cxsetter (Sum Int) (Seq a) (Seq a) a Bool
cxfiltered = cxsetter $ \f k s ->
  Seq.fromList [a | (i, a) <- zip [0..] (Foldable.toList s), f (k <> Sum i) a]
{-# INLINE cxfiltered #-}

-- | /O(n)/. 'Cxtraversal' over the elements of a 'Seq'.
--
-- Cx dual of 'ixtraversed'. Threads the 'Int' index as coindex.
--
-- @
-- 'cxtraverseOf' cxtraversed ≡ 'Seq.traverseWithIndex'
-- @
--
cxtraversed :: Cxtraversal (Sum Int) (Seq a) (Seq b) a b
cxtraversed = cxtraversalVl $ \fakb k fs ->
  Seq.mapWithIndex (\i a -> fakb (fmap (\s -> fromMaybe a (Seq.lookup i s)) fs) (k <> Sum i)) (copure fs)
{-# INLINE cxtraversed #-}

-- | /O(n)/. 'Cxfold' over the elements of a 'Seq'.
--
-- Cx dual of 'ixfolded'. Threads the 'Int' index as coindex.
--
cxfolded :: Cxfold (Sum Int) (Seq a) a
cxfolded = cxfoldVl $ \fakb k fs ->
  Seq.mapWithIndex (\i a -> fakb (fmap (\s -> fromMaybe a (Seq.lookup i s)) fs) (k <> Sum i)) (copure fs)
{-# INLINE cxfolded #-}

---------------------------------------------------------------------
-- Slicing
---------------------------------------------------------------------

-- | Indexed traversal over the first @n@ elements.
--
-- Each element carries its positional index.
slicedTo :: Int -> Ixtraversal' (Sum Int) (Seq a) a
slicedTo n = ixtraversalVl $ \f k m -> case Seq.splitAt n m of
  (l, r) -> (Seq.>< r) . Seq.fromList <$>
    traverse (\(i, a) -> f (k <> Sum i) a) (zip [0..] (Foldable.toList l))
{-# INLINE slicedTo #-}

-- | Indexed traversal over all but the first @n@ elements.
--
-- Each element carries its positional index (starting at @n@).
slicedFrom :: Int -> Ixtraversal' (Sum Int) (Seq a) a
slicedFrom n = ixtraversalVl $ \f k m -> case Seq.splitAt n m of
  (l, r) -> (l Seq.><) . Seq.fromList <$>
    traverse (\(i, a) -> f (k <> Sum (n + i)) a) (zip [0..] (Foldable.toList r))
{-# INLINE slicedFrom #-}

-- | Indexed traversal over elements in range @[i, j)@.
--
-- Each element carries its positional index.
sliced :: Int -> Int -> Ixtraversal' (Sum Int) (Seq a) a
sliced i j = ixtraversalVl $ \f k s -> case Seq.splitAt i s of
  (l, mr) -> case Seq.splitAt (j-i) mr of
    (m, r) -> (\n -> l Seq.>< n Seq.>< r) . Seq.fromList <$>
      traverse (\(idx, a) -> f (k <> Sum (i + idx)) a) (zip [0..] (Foldable.toList m))
{-# INLINE sliced #-}


-- | A 'Seq' is isomorphic to a 'ViewL'
--
-- @'viewl' m ≡ m 'Data.Profunctor.Optic.Operator.^.' 'viewedl'@
--
-- >>> Seq.fromList [1,2,3] ^. viewedl
-- 1 :< fromList [2,3]
--
-- >>> Seq.empty ^. viewedl
-- EmptyL
--
-- >>> EmptyL ^. re viewedl
-- fromList []
--
-- >>> review viewedl $ 1 Seq.:< fromList [2,3]
-- fromList [1,2,3]
--
viewedl :: Iso (Seq a) (Seq b) (ViewL a) (ViewL b)
viewedl = iso viewl $ \xs -> case xs of
  EmptyL      -> mempty
  a Seq.:< as -> a Seq.<| as
{-# INLINE viewedl #-}

-- | A 'Seq' is isomorphic to a 'ViewR'
--
-- @'viewr' m ≡ m 'Data.Profunctor.Optic.Operator.^.' 'viewedr'@
--
-- >>> Seq.fromList [1,2,3] ^. viewedr
-- fromList [1,2] :> 3
--
-- >>> Seq.empty ^. viewedr
-- EmptyR
--
-- >>> EmptyR ^. re viewedr
-- fromList []
--
-- >>> review viewedr $ fromList [1,2] Seq.:> 3
-- fromList [1,2,3]
--
viewedr :: Iso (Seq a) (Seq b) (ViewR a) (ViewR b)
viewedr = iso viewr $ \xs -> case xs of
  EmptyR      -> mempty
  as Seq.:> a -> as Seq.|> a
{-# INLINE viewedr #-}

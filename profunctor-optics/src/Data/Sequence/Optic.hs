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
    -- * Traversal0
  , at
  , ixat
    -- * Traversal
  , traversed
  , ixtraversed
  , slicedTo
  , slicedFrom
  , sliced
    -- * Fold
  , folded
  , ixfolded
    -- * Setter
  , ixmapped
    -- * Dual Optics
    -- ** Colens
  , zipped
    -- ** Cotraversal
  , zippedTraverse
    -- ** Cxsetter
  , cxmapped
    -- ** Cxtraversal
  , cxtraversed
    -- ** Cxfold
  , cxfolded
    -- * Iso
  , viewedl
  , viewedr
) where

import Data.Profunctor.Optic hiding (zipped)
import Data.Profunctor.Optic.Import
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
ixat :: Ixtraversal0' Int (Seq a) a
ixat = ixtraversalVl0 $ \point f k s ->
  case Seq.lookup k s of
    Nothing -> point s
    Just a  -> fmap (\b -> Seq.update k b s) (f k a)
{-# INLINE ixat #-}

---------------------------------------------------------------------
-- Traversal
---------------------------------------------------------------------

-- | /O(n)/. Indexed traversal over the elements of a 'Seq'.
--
ixtraversed :: Ixtraversal Int (Seq a) (Seq b) a b
ixtraversed = ixtraversalVl $ \f k ->
  fmap Seq.fromList . traverse (\(i, a) -> f (k + i) a) . zip [0..] . Foldable.toList
{-# INLINE ixtraversed #-}

---------------------------------------------------------------------
-- Fold
---------------------------------------------------------------------

-- | /O(n)/. Indexed fold over the elements of a 'Seq'.
--
ixfolded :: Ixfold Int (Seq a) a
ixfolded = ixfoldVl $ \f k ->
  traverse (\(i, a) -> f (k + i) a) . zip [0..] . Foldable.toList
{-# INLINE ixfolded #-}

---------------------------------------------------------------------
-- Setter
---------------------------------------------------------------------

-- | /O(n)/. Indexed setter over the elements of a 'Seq'.
--
ixmapped :: Ixsetter Int (Seq a) (Seq b) a b
ixmapped = ixsetter $ \f -> Seq.mapWithIndex f
{-# INLINE ixmapped #-}

---------------------------------------------------------------------
-- Dual optics
---------------------------------------------------------------------

-- | Grate viewing a Seq as a function from Int indices.
-- Requires known length to be representable.
--
zipped :: Int -> Colens (Seq a) (Seq b) (Int -> a) (Int -> b)
zipped n = grate $ \f -> Seq.fromFunction n (\i -> f (\s i' -> Seq.index s i') i)
{-# INLINE zipped #-}

-- | Pointwise 'Cotraversal' over the elements of a 'Seq' at a
-- fixed length. Extends 'zipped' from 'Colens' to 'Cotraversal'.
--
-- Requires known length because 'Seq' is not 'Distributive'
-- (it has variable size).
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
cxmapped :: Cxsetter Int (Seq a) (Seq b) a b
cxmapped = cxsetter Seq.mapWithIndex
{-# INLINE cxmapped #-}

-- | /O(n)/. 'Cxtraversal' over the elements of a 'Seq'.
--
-- Cx dual of 'ixtraversed'. Threads the 'Int' index as coindex.
--
-- @
-- 'cxtraverseOf' cxtraversed ≡ 'Seq.traverseWithIndex'
-- @
--
cxtraversed :: Cxtraversal Int (Seq a) (Seq b) a b
cxtraversed = cxtraversalVl $ \fakb k fs ->
  Seq.mapWithIndex (\i _a -> fakb (fmap (`Seq.index` i) fs) (k + i)) (copure fs)
{-# INLINE cxtraversed #-}

-- | /O(n)/. 'Cxfold' over the elements of a 'Seq'.
--
-- Cx dual of 'ixfolded'. Threads the 'Int' index as coindex.
--
cxfolded :: Cxfold Int (Seq a) a
cxfolded = cxfoldVl $ \fakb k fs ->
  Seq.mapWithIndex (\i _a -> fakb (fmap (`Seq.index` i) fs) (k + i)) (copure fs)
{-# INLINE cxfolded #-}

---------------------------------------------------------------------
-- Slicing
---------------------------------------------------------------------

-- | Traverse the first @n@ elements of a 'Seq'
--
-- >>> fromList [1,2,3,4,5] ^.. slicedTo 2
-- [1,2]
--
-- >>> fromList [1,2,3,4,5] & slicedTo 2 %~ (*10)
-- fromList [10,20,3,4,5]
--
-- >>> fromList [1,2,4,5,6] & slicedTo 10 .~ 0
-- fromList [0,0,0,0,0]
slicedTo :: Int -> Traversal' (Seq a) a
slicedTo n = traversalVl $ \f m -> case Seq.splitAt n m of
  (l, r) -> (Seq.>< r) <$> traverse f l
{-# INLINE slicedTo #-}

-- | Traverse all but the first @n@ elements of a 'Seq'
--
-- >>> fromList [1,2,3,4,5] ^.. slicedFrom 2
-- [3,4,5]
--
-- >>> fromList [1,2,3,4,5] & slicedFrom 2 %~ (*10)
-- fromList [1,2,30,40,50]
--
-- >>> fromList [1,2,3,4,5] & slicedFrom 10 .~ 0
-- fromList [1,2,3,4,5]
slicedFrom :: Int -> Traversal' (Seq a) a
slicedFrom n = traversalVl $ \f m -> case Seq.splitAt n m of
  (l, r) -> (l Seq.><) <$> traverse f r
{-# INLINE slicedFrom #-}

-- | Traverse all the elements numbered from @i@ to @j@ of a 'Seq'
--
-- >>> fromList [1,2,3,4,5] & sliced 1 3 %~ (*10)
-- fromList [1,20,30,4,5]
--
-- >>> fromList [1,2,3,4,5] ^.. sliced 1 3
-- [2,3]
--
-- >>> fromList [1,2,3,4,5] & sliced 1 3 .~ 0
-- fromList [1,0,0,4,5]
sliced :: Int -> Int -> Traversal' (Seq a) a
sliced i j = traversalVl $ \f s -> case Seq.splitAt i s of
  (l, mr) -> case Seq.splitAt (j-i) mr of
    (m, r) -> traverse f m <&> \n -> l Seq.>< n Seq.>< r
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

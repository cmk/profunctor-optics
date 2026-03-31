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
module Data.Tree.Optic (
    -- * Types
    Tree
    -- * Lens
  , root
  , branches
    -- * Traversal
  , flattened
  , ixflattened
    -- * Fold
  , folded
) where

import Data.Profunctor.Optic hiding (folded)
import Data.Profunctor.Optic.Import
import Data.Tree
import Data.Foldable (traverse_)
import Prelude

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> import Data.Tree
-- >>> import Data.Profunctor.Optic

-- | A 'Lens' that focuses on the root of a 'Tree'.
--
-- >>> view root $ Node 42 []
-- 42
--
root :: Lens' (Tree a) a
root = lensVl $ \f (Node a as) -> (`Node` as) <$> f a
{-# INLINE root #-}

-- | A 'Lens' returning the direct descendants of the root of a 'Tree'
--
-- @'Data.Profunctor.Optic.View.view' 'branches' ≡ 'subForest'@
--
branches :: Lens' (Tree a) [Tree a]
branches = lensVl $ \f (Node a as) -> Node a <$> f as
{-# INLINE branches #-}

---------------------------------------------------------------------
-- Traversal
---------------------------------------------------------------------

-- | Pre-order traversal of all values in a 'Tree'.
--
-- >>> over flattened (+1) (Node 1 [Node 2 [], Node 3 [Node 4 []]])
-- Node 2 [Node 3 [],Node 4 [Node 5 []]]
--
flattened :: Traversal (Tree a) (Tree b) a b
flattened = traversalVl go
  where go f (Node a cs) = Node <$> f a <*> traverse (go f) cs
{-# INLINE flattened #-}

-- | Depth-indexed traversal of all values in a 'Tree'.
-- The index is the depth from the root (root = 0).
--
ixflattened :: Ixtraversal Int (Tree a) (Tree b) a b
ixflattened = ixtraversalVl (\f k -> go k f)
  where go d f (Node a cs) = Node <$> f d a <*> traverse (go (d + 1) f) cs
{-# INLINE ixflattened #-}

---------------------------------------------------------------------
-- Fold
---------------------------------------------------------------------

-- | Fold over all values in a 'Tree' (pre-order).
--
-- @'Data.Profunctor.Optic.Fold.toListOf' 'folded' ≡ 'flatten'@
--
folded :: Fold (Tree a) a
folded = foldVl go
  where go f (Node a cs) = f a *> traverse_ (go f) cs
{-# INLINE folded #-}

---------------------------------------------------------------------
-- Dual optics
---------------------------------------------------------------------

-- TODO: zipsTree :: Colens (Tree a) (Tree b) a b
-- Pointwise zipping of trees. Zips structurally — root with root,
-- children with children. Mismatched shapes truncate to the shorter tree.
-- Requires careful handling of subforest zipping; deferred for now.

-- Note: no Cofold or Cxfold for Tree.
--
-- A Cofold requires a Cotraversal-compatible structure, which in turn
-- needs pointwise zipping (Distributive or a fixed shape). Trees are
-- recursive with variable branching factor, so there is no canonical
-- way to zip two trees without truncating or padding. The same issue
-- blocks Cotraversal (see TODO above for zipsTree). If a fixed-shape
-- Cotraversal is added in the future, the corresponding Cxfold can
-- be derived from it.

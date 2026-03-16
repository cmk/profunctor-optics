{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.Tree.Optic (
    root
  , branches
) where

import Data.Profunctor.Optic
import Data.Tree

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

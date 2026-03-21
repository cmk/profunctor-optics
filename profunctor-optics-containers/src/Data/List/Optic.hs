{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.List.Optic (
    toListOf
  , ixlists
  , at
  , iat
  , imapped 
  , ifiltered 
  , itraversed
  , ifolded
) where

import Data.Profunctor.Optic
import Data.Maybe (listToMaybe)

-- $setup
-- >>> :set -XNoOverloadedStrings
-- >>> :set -XTypeApplications
-- >>> :set -XFlexibleContexts
-- >>> import Data.Profunctor.Optic

-- | /O(log n)/. Affine traversal into the value at a key of a list.
--
at :: Int -> Traversal0' [a] a
at k = traversalVl0 $ \point f xs -> if k < 0 then point xs else
  let go [] _ = point []
      go (a:as) 0 = (:as) <$> f a 
      go (a:as) i = (a:) <$> (go as $! i - 1)
   in go xs k
{-# INLINE at #-}

-- | /O(log n)/. Indexed affine traversal into the value at a key of a list.
--
-- >>> iover (iat 1) (<>) [1,2,3]
-- [1,3,3]
-- >>> iover (iat 5) (<>) [1,2,3]
-- [1,2,3]
--
iat :: Int -> Ixtraversal0' Int [a] a
iat i = ixtraversal0' (\s -> listToMaybe [(n, x) | (n, x) <- zip [0..] s, n == i]) (\s a -> zipWith (\j x -> if i == j then a else x) [0..] s)
{-# INLINE iat #-}

-- | /O(n)/. 'Ixsetter' over the values of a list.
--
-- >>> iover imapped (<>) $ [0,3,4]
-- [0,4,6]
--
imapped :: Ixsetter Int [a] [b] a b
imapped = ixsetter $ \f -> zipWith f [0..]
{-# INLINE imapped #-}

-- | /O(n)/. 'Ixsetter' filtering the values of a list.
--
ifiltered :: Ixsetter Int [a] [a] a Bool
ifiltered = ixsetter $ \f xs -> [x | (i, x) <- zip [0..] xs, f i x]
{-# INLINE ifiltered #-}

-- | /O(n)/. 'Ixtraversal' over the values of a list.
--
itraversed :: Ixtraversal Int [a] [b] a b
itraversed = ixtraversalVl $ \f -> traverse (uncurry f) . zip [0..]
{-# INLINE itraversed #-}

-- | /O(n)/. 'Ixfold' over the values of a list.
--
-- >>> ilists ifolded [0,3,4]
-- [(0,0),(1,3),(2,4)]
-- >>> ilists ifolded []
-- []
--
ifolded :: Ixfold Int [a] a
ifolded = ixfoldVl $ \f -> traverse (uncurry f) . zip [0..]
{-# INLINE ifolded #-}

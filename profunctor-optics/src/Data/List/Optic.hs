{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeFamilies          #-}
module Data.List.Optic (
    at
  , iat
  , imapped
  , ifiltered
  , itraversed
  , ifolded
    -- * Sort-based operators
  , sortingOfL
  , sortingDescOfL
  , groupingOfL
  , nubbingOfL
  , sortingString
) where

import Data.Profunctor.Optic
import Data.Profunctor.Optic.Import
import Data.Profunctor.Optic.Sort (sortingRep)
import Data.Maybe (listToMaybe)
import Data.Ord (Down(..))
import qualified Data.Map.Strict as Map
import Prelude

-- | /O(n)/. Affine traversal into the value at an index of a list.
--
at :: Int -> Traversal0' [a] a
at k = traversalVl0 $ \point f xs -> if k < 0 then point xs else
  let go [] _ = point []
      go (a:as) 0 = (:as) <$> f a
      go (a:as) i = (a:) <$> (go as $! i - 1)
   in go xs k
{-# INLINE at #-}

-- | /O(n)/. Indexed affine traversal into the value at an index.
--
iat :: Int -> Ixtraversal0' Int [a] a
iat i = ixtraversal0' (\s -> listToMaybe [(n, x) | (n, x) <- zip [0..] s, n == i]) (\s a -> zipWith (\j x -> if i == j then a else x) [0..] s)
{-# INLINE iat #-}

-- | /O(n)/. 'Ixsetter' over the values of a list.
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
ifolded :: Ixfold Int [a] a
ifolded = ixfoldVl $ \f -> traverse (uncurry f) . zip [0..]
{-# INLINE ifolded #-}

---------------------------------------------------------------------
-- Sort-based operators
---------------------------------------------------------------------

-- | Sort a list through a lens. Returns @[]@ on empty input.
sortingOfL :: Ord a => Lens' s a -> [s] -> [[s]]
sortingOfL _ [] = []
sortingOfL o xs = Map.elems $ Map.fromListWith (flip (++))
  [(s ^. o, [s]) | s <- xs]

-- | Sort a list in descending order through a lens.
sortingDescOfL :: Ord a => Lens' s a -> [s] -> [[s]]
sortingDescOfL _ [] = []
sortingDescOfL o xs = Map.elems $ Map.fromListWith (flip (++))
  [(Down (s ^. o), [s]) | s <- xs]

-- | Group a list through a lens.
groupingOfL :: Ord a => Lens' s a -> [s] -> [[s]]
groupingOfL = sortingOfL

-- | Deduplicate a list through a lens, keeping first per group.
nubbingOfL :: Ord a => Lens' s a -> [s] -> [s]
nubbingOfL _ [] = []
nubbingOfL o xs = map head $ sortingOfL o xs

-- | Sort a 'String' by a key on each character.
sortingString :: Ord k => (Char -> k) -> String -> Map.Map k String
sortingString = sortingRep length (\s i -> s !! i) id

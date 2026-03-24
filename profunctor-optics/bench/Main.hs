{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

-- | Comprehensive profunctor-optics benchmark suite.
module Main (main) where

import Criterion.Main

import Data.Profunctor.Optic
import Data.Profunctor.Optic.Bench
import Data.Profunctor.Optic.Fold (foldsWithKey)
import Data.Profunctor.Optic.Setter (sets, setsWithKey)
import Data.List.Optic (sorts)
import qualified Data.Map.Optic as MO
import qualified Data.Map.Strict as Map

main :: IO ()
main = defaultMain
  [ lensGroup
  , traversalGroup
  , traversal0Group
  , foldGroup
  , ixTraversalGroup
  , ixFoldGroup
  , compositionGroup
  , sortGroup
  , containerGroup
  ]

---------------------------------------------------------------------
-- Test optics and data
---------------------------------------------------------------------

fstL :: Lens' (Int, String) Int
fstL = lensVl $ \f (a, b) -> (\a' -> (a', b)) <$> f a

pair :: (Int, String)
pair = (42, "hello")

list100 :: [Int]
list100 = [1..100]

list1K :: [Int]
list1K = [1..1000]

list10K :: [Int]
list10K = [1..10000]

pairs100 :: [(Int, String)]
pairs100 = [(i `mod` 20, show i) | i <- [1..100]]

pairs1K :: [(Int, String)]
pairs1K = [(i `mod` 50, show i) | i <- [1..1000]]

map100 :: Map.Map Int String
map100 = Map.fromList [(i, show i) | i <- [1..100]]

mapStr100 :: Map.Map String Int
mapStr100 = Map.fromList [(show i, i) | i <- [1..100]]

---------------------------------------------------------------------
-- S16.5: Lens/Prism/Traversal0
---------------------------------------------------------------------

lensGroup :: Benchmark
lensGroup = bgroup "lens"
  [ let (optic, direct) = benchLens fstL fst (\(_, b) a -> (a, b)) (+1)
    in bgroup "fstL"
      [ bench "view-optic"  $ nf (fst optic)  pair
      , bench "view-direct" $ nf (fst direct)  pair
      , bench "over-optic"  $ nf (snd optic)  pair
      , bench "over-direct" $ nf (snd direct)  pair
      ]
  ]

traversal0Group :: Benchmark
traversal0Group = bgroup "traversal0"
  [ let (optic, direct) = benchTraversal0 just id
    in bgroup "just"
      [ bench "preview-optic"  $ nf optic  (Just (42 :: Int))
      , bench "preview-direct" $ nf direct (Just (42 :: Int))
      ]
  ]

---------------------------------------------------------------------
-- S16.6: Traversal
---------------------------------------------------------------------

traversalGroup :: Benchmark
traversalGroup = bgroup "traversal"
  [ let (optic, direct) = benchTraversal traversed (map :: (Int -> Int) -> [Int] -> [Int]) (+1)
    in bgroup "traversed"
      [ bgroup "100"
        [ bench "optic"  $ nf optic  list100
        , bench "direct" $ nf direct list100
        ]
      , bgroup "1K"
        [ bench "optic"  $ nf optic  list1K
        , bench "direct" $ nf direct list1K
        ]
      , bgroup "10K"
        [ bench "optic"  $ nf optic  list10K
        , bench "direct" $ nf direct list10K
        ]
      ]
  ]

---------------------------------------------------------------------
-- S16.7: Fold
---------------------------------------------------------------------

foldGroup :: Benchmark
foldGroup = bgroup "fold"
  [ bgroup "lists-on-list-100"
    [ bench "lists-optic"  $ nf (lists folded) list100
    , bench "foldr-(:)-[]" $ nf (foldr (:) []) list100
    ]
  , bgroup "lists-on-map-100"
    [ bench "lists-optic"  $ nf (lists (MO.values)) map100
    , bench "Map.elems"    $ nf Map.elems map100
    , bench "toList"       $ nf (foldr (:) [] . Map.elems) map100
    ]
  ]

---------------------------------------------------------------------
-- S16.8: Indexed traversal (Conjoin overhead)
---------------------------------------------------------------------

ixTraversalGroup :: Benchmark
ixTraversalGroup = bgroup "ix-traversal"
  [ let mapData = mapStr100
    in bgroup "Map-String-key"
      [ bench "indexed-setsWithKey" $ nf (setsWithKey MO.itraversed (\k a -> length k + a)) mapData
      , bench "direct-mapWithKey"   $ nf (Map.mapWithKey (\k a -> length k + a)) mapData
      , bench "direct-fmap"         $ nf (fmap (+1)) mapData
      ]
  ]

ixFoldGroup :: Benchmark
ixFoldGroup = bgroup "ix-fold"
  [ let mapData = mapStr100
    in bgroup "Map-ifolded"
      [ bench "indexed"     $ nf (foldsWithKey MO.ifolded (\k a -> k ++ show a)) mapData
      , bench "direct"      $ nf (Map.foldlWithKey' (\r k a -> r ++ k ++ show a) "") mapData
      ]
  ]

---------------------------------------------------------------------
-- S16.9: Composition
---------------------------------------------------------------------

compositionGroup :: Benchmark
compositionGroup = bgroup "composition"
  [ let listTraversed :: Traversal' [(Int, String)] (Int, String)
        listTraversed = traversed
        (optic, direct) = benchCompose2 listTraversed first' (+1)
          (\f -> map (\(a,b) -> (f a, b)))
    in bgroup "traversed.first"
      [ bench "optic"  $ nf optic  pairs100
      , bench "direct" $ nf direct pairs100
      ]
  ]

---------------------------------------------------------------------
-- S16.10: Sort carrier
---------------------------------------------------------------------

sortGroup :: Benchmark
sortGroup = bgroup "sort-carrier"
  [ bgroup (show n)
    [ let (optic, direct) = benchSortVsDirect n (`mod` 50)
      in bgroup "mkSortN"
        [ bench "optic"  $ nf optic  ()
        , bench "direct" $ nf direct ()
        ]
    ]
  | n <- [100, 1000, 10000]
  ]

---------------------------------------------------------------------
-- S16.11: Container benchmarks
---------------------------------------------------------------------

containerGroup :: Benchmark
containerGroup = bgroup "containers"
  [ bgroup "sorts"
    [ let (optic, direct) = benchSortingOfL fstL pairs1K
      in bgroup "1K"
        [ bench "optic"  $ nf optic  pairs1K
        , bench "direct" $ nf direct pairs1K
        ]
    ]
  , bgroup "toMapOf"
    [ let (optic, direct) = benchToMapOfL fstL
      in bgroup "1K"
        [ bench "optic"  $ nf optic  pairs1K
        , bench "direct" $ nf direct pairs1K
        ]
    ]
  ]

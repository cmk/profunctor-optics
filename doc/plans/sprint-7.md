# Sprint 7 — Benchmarks

## Scope

Criterion benchmarks for the most promising Sort types, operators,
and container integrations. Compare against direct implementations,
Data.List.sort, discrimination library, and containers merge API
to establish the overhead (or lack thereof) of the profunctor
abstraction layer.

## Rationale

The optics abstraction adds layers of indirection (carrier
construction, profunctor composition, materialization). We need to
measure whether GHC optimizes these away or whether there's
meaningful overhead. The strings package showed zero-cost splitting
isos and 6-7x overhead for cotraversals vs machine instructions —
we should establish similar baselines for sorting.

## Stories

| ID    | Module / target               | Description                                        |
|-------|-------------------------------|----------------------------------------------------|
| S7.1  | bench/Sort1.hs                | Sort1 vs Data.List.sort vs discrimination          |
| S7.2  | bench/Sort3.hs                | Sort3 sortingVector vs V.modify (intro sort)       |
| S7.3  | bench/Map.hs                  | toMapOf vs Map.fromListWith                        |
| S7.4  | bench/Merge.hs                | mergingOf vs direct Map.merge                      |
| S7.5  | bench/Compose.hs              | Optic composition overhead (sortingOf vs raw Sort1)|
| S7.6  | bench/Array.hs                | sortingRep for Vector/PrimArray/Array               |

## Benchmark groups

### S7.1 — Sort1 vs alternatives

```
Sort1 sortingOf (Lens):
  - sortingOf fstL on NonEmpty (Int, String)
  - varying sizes: 100, 1K, 10K, 100K elements
  - varying key cardinality: 10, 100, 1000 distinct keys

Baselines:
  - Data.List.sortOn fst (O(n log n) comparison sort)
  - discrimination sortWith fst (O(n) radix sort)
  - direct mkSort1 without optic wrapper
```

### S7.2 — Sort3 Vector sorting

```
Sort3 sortingVector:
  - sortingVector fst on Vector (Int, String)
  - varying sizes: 100, 1K, 10K, 100K

Baselines:
  - V.modify (VA.sortBy (comparing fst)) (in-place intro sort)
  - Map.fromListWith (++) . map (\x -> (fst x, [x])) . V.toList
  - discrimination sortWith on V.toList
```

### S7.3 — Container construction

```
toMapOf:
  - toMapOf fstL on NonEmpty (Int, String)
  - varying sizes: 100, 1K, 10K

Baselines:
  - Map.fromListWith (<>) . map (\s -> (fst s, s:|[])) . NE.toList
  - Map.fromList . map (\g -> (NE.head g ^. fstL, g)) . sortingOf fstL
```

### S7.4 — Merge operations

```
mergingOf with tactics:
  - innerMerge on two NonEmpty (Int, String) inputs
  - outerMerge with separate left/right/both handlers
  - varying sizes: 100, 1K, 10K per side

Baselines:
  - Map.merge directly (build Maps by hand, then merge)
  - joiningOf (old-style tagged Either approach)
```

### S7.5 — Optic composition overhead

```
Measure the cost of the profunctor abstraction:
  - sortingOf fstL vs. runSort1 (fstL mkSort1) (manual key+carrier)
  - cosortingOf bits8 carrier vs. bits8 carrier directly
  - sortingUnder grate8 carrier vs. grate8 carrier directly

These should ideally be identical (the optic is just function
application), but INLINE pragmas and specialization matter.
```

### S7.6 — Array backend comparison

```
sortingRep across backends:
  - Boxed Vector (V.generate / V.!)
  - Unboxed Vector (VU.generate / VU.!)
  - PrimArray (generatePrimArray / indexPrimArray)
  - Array (genArray / (!))
  - Same data, same key function, varying sizes

This measures materialization cost across backends.
```

## Benchmark infrastructure

```haskell
-- bench/Main.hs
main :: IO ()
main = defaultMain
  [ sort1Benchmarks
  , sort3Benchmarks
  , mapBenchmarks
  , mergeBenchmarks
  , composeBenchmarks
  , arrayBenchmarks
  ]
```

Add to cabal:
```
benchmark sort-bench
  type:              exitcode-stdio-1.0
  main-is:           Main.hs
  other-modules:     ...
  ghc-options:       -Wall -O2 -threaded -rtsopts
  hs-source-dirs:    bench
  default-language:  Haskell2010
  build-depends:
      base
    , criterion           >= 1.5
    , containers
    , deepseq
    , discrimination
    , profunctors
    , profunctor-optics
    , profunctor-optics-sort
    , profunctor-optics-strings
    , scheme-extensions
    , vector
    , primitive
    , array
```

## Expected results and what to look for

| Benchmark | Expected | Red flag |
|---|---|---|
| sortingOf vs Data.List.sortOn | 1-3x slower (Map.fromListWith overhead) | >5x slower |
| sortingOf vs discrimination sort | 10-100x slower (we use Map, they use radix) | N/A (different algo) |
| optic wrapper vs raw carrier | ~1.0x (zero-cost abstraction) | >1.2x (missing INLINE) |
| toMapOf vs Map.fromListWith | ~1.0x (same underlying operation) | >2x |
| mergingOf vs direct Map.merge | ~1.0x (thin wrapper) | >1.5x |
| sortingVector vs V.modify sort | 5-20x slower (materialization overhead) | >50x |
| Sort3 mkSort3N vs mkSort1 | Sort3 slower (function indirection) | >10x |

## Work order

1. Set up criterion infrastructure (cabal, Main.hs)
2. S7.5 — Composition overhead (cheapest to measure, most important)
3. S7.1 — Sort1 benchmarks
4. S7.3 — toMapOf benchmarks
5. S7.4 — Merge benchmarks
6. S7.2 — Sort3 Vector benchmarks
7. S7.6 — Array backend comparison
8. Analyze results, add INLINE pragmas where needed, re-benchmark

## Key files

- `profunctor-optics-sort/bench/` — new benchmark directory
- `profunctor-optics-sort/profunctor-optics-sort.cabal` — benchmark stanza
- `profunctor-optics-strings/bench/` — reference (existing benchmarks)

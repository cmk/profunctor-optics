# Sprint 16 — Bench.hs and library profiling

## Scope

Flesh out `Data.Profunctor.Optic.Bench` with reusable benchmark
builders for all optic families. Build a comprehensive benchmark
suite in `bench/Main.hs` that profiles the core library. Pay
particular attention to indexed/coindexed traversals and folds,
which route through `Combinator.hs` transforms (`repsWithKey`,
`corepsWithKey`, `represent`, `corepresent`, `Conjoin`) that
may introduce overhead.

## Rationale

The strings benchmarks revealed 6-7x overhead for cotraversals
vs coindexed optics. The Sort benchmarks showed Sort carriers
are zero-cost. We haven't profiled the core indexed/coindexed
machinery — `(%)`, `(#)`, `overWithKey`, `reoverWithKey`,
`repsWithKey`, `corepsWithKey` — which goes through `Conjoin`
and `Coindex` wrapping/unwrapping. These are the hotpath for
any user composing indexed optics.

## Stories

| ID     | Target | Description |
|--------|--------|-------------|
| S16.1  | Bench.hs | Optic abstraction builders (lens, traversal, fold) |
| S16.2  | Bench.hs | Composition builders |
| S16.3  | Bench.hs | Container-specific baselines |
| S16.4  | Bench.hs | Scaling profile builder |
| S16.5  | bench/Main.hs | Lens/Prism/Traversal0 overhead benchmarks |
| S16.6  | bench/Main.hs | Traversal overhead (Star carrier) |
| S16.7  | bench/Main.hs | Cotraversal overhead (Costar carrier) |
| S16.8  | bench/Main.hs | Indexed optic overhead (Conjoin, repsWithKey) |
| S16.9  | bench/Main.hs | Coindexed optic overhead (Coindex, corepsWithKey) |
| S16.10 | bench/Main.hs | Sort carrier benchmarks (port from sandbox) |
| S16.11 | bench/Main.hs | Container benchmarks (Map, IntMap, Set) |
| S16.12 | Bench.hs Haddock | Complete performance documentation |

## S16.1 — Optic abstraction builders

```haskell
-- | Compare view/over through a Lens vs direct get/set.
-- Returns (optic-based, direct) function pairs.
benchLens :: Lens' s a -> (s -> a) -> (a -> a) -> s
          -> ((s -> a, s -> s), (s -> a, s -> s))

-- | Compare traverse through a Traversal vs direct.
benchTraversal :: Traversal' s a -> ((a -> a) -> s -> s) -> (a -> a) -> s
               -> (s -> s, s -> s)

-- | Compare fold through a Fold vs direct.
benchFold :: Fold s a -> (s -> [a]) -> s
          -> (s -> [a], s -> [a])

-- | Compare preview through a Traversal0 vs direct.
benchTraversal0 :: Traversal0' s a -> (s -> Maybe a) -> s
                -> (s -> Maybe a, s -> Maybe a)

-- | Compare over through a Colens vs direct.
benchColens :: Colens' s a -> ((a -> a) -> s -> s) -> (a -> a) -> s
            -> (s -> s, s -> s)
```

## S16.2 — Composition builders

```haskell
-- | Compare composed optic vs direct composed function.
benchCompose2 :: Optic (->) s t a b -> Optic (->) a b c d
              -> (c -> d) -> s -> (s -> t, s -> t)

-- | Compare indexed composition (%) vs plain (.).
benchIxCompose :: Ixoptic (->) k s t a b -> Ixoptic (->) k a b c d
               -> (k -> c -> d) -> s -> ...

-- | Compare coindexed composition (#) vs plain (.).
benchCxCompose :: Cxoptic (->) k s t a b -> Cxoptic (->) k a b c d
               -> (k -> c -> d) -> s -> ...
```

## S16.3 — Container baselines

```haskell
-- | Compare sortingOfL vs Data.List.sortOn + manual grouping.
benchSortingOfL :: Ord a => Lens' s a -> [s]
                -> ([s] -> [[s]], [s] -> [[s]])

-- | Compare toMapOfL vs direct Map.fromListWith.
benchToMapOfL :: Ord a => Lens' s a -> [s]
              -> ([s] -> Map a [s], [s] -> Map a [s])

-- | Compare innerMergeL vs direct Map.merge.
benchInnerMergeL :: Ord a => Lens' s a -> Lens' t a -> [s] -> [t]
                 -> (() -> Map a c, () -> Map a c)
```

## S16.4 — Scaling profile builder

```haskell
-- | Build benchmarks at multiple sizes.
-- Returns a list of (size, benchmark-pair) for feeding to
-- Criterion's bgroup.
benchScaling :: [Int]                    -- ^ sizes
             -> (Int -> input)           -- ^ generate input of size n
             -> (input -> output)        -- ^ function to benchmark
             -> [(Int, input -> output)]
```

## S16.5–S16.9 — Core library benchmarks

### S16.5 — Lens/Prism/Traversal0 (Strong/Choice/Affine)

```
Benchmark                    What it measures
─────────                    ────────────────
view fstL pair               Lens view overhead
over fstL (+1) pair          Lens over overhead
preview just (Just x)        Traversal0 preview overhead
set just x (Just y)          Traversal0 set overhead
```

Expected: ~0 overhead (these are function application).

### S16.6 — Traversal (Star carrier)

```
Benchmark                    What it measures
─────────                    ────────────────
over traversed (+1) [1..n]   Traversal over, varying n
sets traversed (+1) [1..n]   Setter sets overhead
traverses traversed f xs     Raw Star traverse
```

Expected: O(n), comparable to `fmap`.

### S16.7 — Cotraversal (Costar carrier)

```
Benchmark                    What it measures
─────────                    ────────────────
over bits8 not w             Cotraversal over on Word8
over grate8 id w             Colens over on Word8
cotraverses bits8 f fs       Raw Costar cotraverse
```

Expected: ~21-44 ns/element (from strings benchmarks).

### S16.8 — Indexed optics (Conjoin, repsWithKey)

THIS IS THE KEY RISK AREA. The indexed operators go through:

```
overWithKey o f = (unConjoin #. corepresent o .# Conjoin) f mempty
repsWithKey o f = curry (reps o $ uncurry f) mempty
```

`Conjoin` wrapping + `corepresent` + `unConjoin` unwrapping.
Need to measure:

```
Benchmark                            What it measures
─────────                            ────────────────
over (itraversed) (+1) map           Non-indexed Map traversal
overWithKey itraversed (+) map       Indexed Map traversal (Conjoin)
overWithKey (f % g) h map            Composed indexed traversal
iover itraversed f map               Indexed traversal via iover
lists ifolded map                    Non-indexed fold
listsWithKey ifolded map             Indexed fold (Conjoin)
foldsWithKey ifolded f map           Indexed fold aggregation
```

Compare against direct `Map.mapWithKey`, `Map.foldlWithKey`.
The overhead from `Conjoin`/`unConjoin` and `mempty` seeding
should be measurable.

### S16.9 — Coindexed optics (Coindex, corepsWithKey)

```
Benchmark                            What it measures
─────────                            ────────────────
reoverWithKey ibits8 f w             Coindexed over (Conjoin flip)
corepsWithKey ibits8 f corep         Coindexed corep extraction
cofoldsWithKey (rxfrom f) g r m      Coindexed cofold (Coindex)
```

Compare against direct function calls. The `Coindex` wrapping
and `(<<<<)` composition operator may add overhead.

### S16.10 — Sort carrier (port from sandbox)

Port the three benchmarks from profunctor-optics-sort/bench:
- Carrier overhead: mkSortN vs direct Map.fromListWith
- Optic composition: bare vs grate8 vs bits8 vs ibits8
- Pipeline: single vs two-pass via (%.)

### S16.11 — Container benchmarks

```
Benchmark                    What it measures
─────────                    ────────────────
sortingOfL fstL xs           List sorting through lens
toMapOfL fstL xs             Map construction through lens
innerMergeL lo ro f xs ys    Merge through lenses
groupSortBy cmp grp xs       Comparator-based sort
uniqueSort xs                Sort + dedup
at k map                     Map.at via optic vs Map.lookup
```

Vary sizes: 100, 1K, 10K.

## S16.12 — Haddock documentation hub

The Bench.hs module Haddock should document:

1. **Performance hierarchy** (already there, expand)
2. **Known overhead sources:**
   - `Conjoin` wrapping in indexed ops
   - `Coindex` wrapping in coindexed ops
   - `Distributive` reconstruction in cotraversals
   - `Map.fromListWith` in Sort carriers
3. **Diagnostic guide:**
   - "My optic is slow" → check which carrier path
   - "My indexed traversal is slow" → Conjoin overhead
   - "My cotraversal is slow" → prefer coindexed (ibitsN)
4. **How to benchmark your own optics:**
   - Import Bench.hs builders
   - Wrap in Criterion.nf
   - Compare pairs

## Work order

1. S16.1 — Optic abstraction builders
2. S16.2 — Composition builders
3. S16.3 — Container baselines
4. S16.4 — Scaling builder
5. S16.5 — bench/Main.hs: Lens/Prism/Traversal0
6. S16.6 — bench/Main.hs: Traversal
7. S16.7 — bench/Main.hs: Cotraversal
8. S16.8 — bench/Main.hs: Indexed (THE RISK AREA)
9. S16.9 — bench/Main.hs: Coindexed
10. S16.10 — bench/Main.hs: Sort carrier (port)
11. S16.11 — bench/Main.hs: Containers
12. S16.12 — Haddock documentation
13. Run full suite, analyze, add INLINE pragmas where needed
14. Re-run, document final numbers

## Expected results and red flags

| Benchmark | Expected | Red flag |
|---|---|---|
| Lens view/over | ~0 overhead | >2x |
| Traversal over | ~1.0x vs fmap | >2x |
| Cotraversal over | ~21-44 ns/elem | >100 ns/elem |
| Indexed traversal (Conjoin) | ~1.0-2.0x vs non-indexed | >5x |
| Coindexed (Coindex) | ~1.0-2.0x vs non-indexed | >5x |
| Indexed composition (%) | ~1.0x vs (.) | >3x |
| Coindexed composition (#) | ~1.0x vs (.) | >3x |
| Sort carrier | ~1.0-1.8x vs direct | >3x |
| sortingOfL | ~1.0x vs sortOn+group | >3x |
| toMapOfL | ~1.0x vs fromListWith | >2x |

The indexed/coindexed rows are the unknowns. Everything else
has been measured.

## Key files

- `profunctor-optics/src/Data/Profunctor/Optic/Bench.hs` — builders
- `profunctor-optics/bench/Main.hs` — benchmark suite (new)
- `profunctor-optics/profunctor-optics.cabal` — benchmark stanza
- `profunctor-optics/src/Data/Profunctor/Optic/Combinator.hs` — (%), (#), Conjoin, Coindex hotpath
- `profunctor-optics/src/Data/Profunctor/Optic/Carrier.hs` — Sort, Index, Coindex types

## Dependencies for benchmark suite

```
criterion, containers, profunctor-optics, profunctor-optics-strings,
scheme-extensions, deepseq
```

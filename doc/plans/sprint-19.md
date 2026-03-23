# Sprint 19 — Container optic modules

## Scope

Fill API gaps in the 7 container optic modules to achieve consistency
across containers and with the core library.

## Stories

| ID | Target | Description |
|---|---|---|
| S19.1 | IntMap.Optic | Uncomment range queries (lookedLT/LE/GE/GT, updateLooked) |
| S19.2 | IntMap.Optic | Uncomment ixaltered', fix validated stub |
| S19.3 | IntMap.Optic | Add sort-based fold/mconcat operators (parity with Map) |
| S19.4 | Sequence.Optic | Add `at`/`ixat` for element access by index |
| S19.5 | Sequence.Optic | Add `ixtraversed`, `ixfolded`, `ixmapped` (parity with List) |
| S19.6 | Sequence.Optic | Add `folded` (non-indexed Fold) |
| S19.7 | Tree.Optic | Add recursive traversal over all nodes |
| S19.8 | Tree.Optic | Add fold over all tree values |
| S19.9 | Tree.Optic | Add depth-indexed traversal |
| S19.10 | List.Optic | Export non-indexed `traversed`, `folded`, `mapped` wrappers |
| S19.11 | Map/IntMap.Optic | Unify sort operator naming with sprint 18 renames |
| S19.12 | All | Property tests for container optics |

## S19.1–S19.3 — IntMap parity with Map

IntMap.Optic has several commented-out functions that exist in Map.Optic.
The IntMap API supports these operations — they were likely deferred
rather than impossible.

Commented out (lines 21–25, 40):
- `updateLooked`, `lookedLT`, `lookedLE`, `lookedGE`, `lookedGT`
- `ixaltered'`

Note: IntMap doesn't have `lookupLT` etc. in `Data.IntMap`, so range
queries may need a different implementation (convert to Map, or binary
search on keys). Investigate feasibility before uncommenting.

`validated` on line 117 is `filtered (const True)` — a stub. Either
implement proper validation or remove.

Missing sort operators vs Map: `foldSorting`, `foldSorting1`,
`mconcatSorting`.

## S19.4–S19.6 — Sequence indexed optics

Seq supports efficient index-based access (`Seq.index`, `Seq.adjust`,
`Seq.update`) making indexed optics natural:

```haskell
at :: Int -> Traversal0' (Seq a) a
ixat :: Int -> Ixtraversal0' Int (Seq a) a
ixtraversed :: Ixtraversal Int (Seq a) (Seq b) a b
ixfolded :: Ixfold Int (Seq a) a
ixmapped :: Ixsetter Int (Seq a) (Seq b) a b
folded :: Fold (Seq a) a
```

## S19.7–S19.9 — Tree recursive optics

```haskell
-- Recursive traversal of all nodes (pre-order)
flattened :: Traversal' (Tree a) a

-- Fold over all values in the tree
folded :: Fold (Tree a) a

-- Depth-indexed traversal (index = depth from root)
ixflattened :: Ixtraversal Int (Tree a) (Tree b) a b
```

Implementation: `flattened` can use `traversalVl` with the existing
`Data.Tree.unfoldTree`/`foldTree` or manual recursion through
`rootLabel`/`subForest`.

## S19.10 — List non-indexed wrappers

List.Optic only exports indexed variants. Add thin wrappers or
re-exports for users who don't need indices:

```haskell
traversed :: Traversal [a] [b] a b  -- re-export from Traversal
folded :: Fold [a] a                -- re-export from Fold
mapped :: Setter [a] [b] a b       -- re-export from Setter
```

## S19.11 — Unify sort operator naming

Map.Optic uses `'` suffix (`toMapOf'`, `foldSorting'`), Sort.hs uses
`L` suffix, sprint 18 renames to active verbs. Apply the same rename
scheme here:

| Map.Optic current | Sprint 18 name |
|---|---|
| `toMapOf'` | `toMapOf` |
| `countingOf'` | `countsOf` |
| `foldSorting'` | `foldSorts` |
| `foldSorting1'` | `foldSorts1` |
| `mconcatSorting'` | `mconcatSorts` |
| `mergingOf'` | `merges` |
| `innerMerge'` | `innerMerges` |
| `outerMerge'` | `outerMerges` |
| `leftMerge'` | `leftMerges` |
| `rightMerge'` | `rightMerges` |

## S19.12 — Property tests

Add hedgehog property tests for:
- Map/IntMap: alteredF round-trip, ixtraversed identity, at/ixat laws
- Sequence: sliced identity, at round-trip
- Tree: root lens laws
- List: ixtraversed identity, at round-trip

## Work order

Phase 1 — IntMap parity:
  1. S19.1 (range queries)
  2. S19.2 (ixaltered', validated)
  3. S19.3 (sort fold operators)

Phase 2 — Sequence/Tree:
  4. S19.4 (Seq at/ixat)
  5. S19.5 (Seq indexed optics)
  6. S19.6 (Seq folded)
  7. S19.7–S19.9 (Tree recursive optics)

Phase 3 — Consistency:
  8. S19.10 (List non-indexed wrappers)
  9. S19.11 (naming unification with sprint 18)

Phase 4 — Tests:
  10. S19.12 (property tests)

## Key files

- `profunctor-optics/src/Data/IntMap/Optic.hs`
- `profunctor-optics/src/Data/Sequence/Optic.hs`
- `profunctor-optics/src/Data/Tree/Optic.hs`
- `profunctor-optics/src/Data/List/Optic.hs`
- `profunctor-optics/src/Data/Map/Optic.hs`
- `profunctor-optics/test/Test/Data/*/Optic.hs`

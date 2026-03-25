# Sprint 25 — Container optic cleanup: apply Map patterns to all container types

## Scope

Apply all the cleanup, naming, structural, and API design work done
on `Data.Map.Optic` to the remaining container optic modules:
IntMap, IntSet, Set, List, Sequence, and Tree.

## Background

Over the past session, Map.Optic was comprehensively refactored.
This sprint enumerates each change and specifies the analogous work
for the other container types. Some changes were already partially
applied during earlier sprints; this sprint completes the job.

## Checklist of changes to apply

### 1. Re-export container types

Each module should re-export its main container type in a `-- * Types`
section at the top of the export list.

| Module | Type | Status |
|--------|------|--------|
| IntMap | `IM.IntMap` | DONE |
| IntSet | `IS.IntSet` | DONE |
| Set | `Set.Set` | DONE |
| Sequence | `Seq` | DONE |
| Tree | `Tree` | DONE |
| List | — (Prelude) | N/A |

### 2. Diamond export/source structure

Exports and source code should follow the adjunction diamond:

```
-- * Left Adjoint Optics
-- * Right Adjoint Optics
-- * Adjoint Optics
-- * Operators
```

| Module | Status |
|--------|--------|
| IntMap | TODO |
| IntSet | TODO (small module, may only have Left + Right) |
| Set | TODO (small module) |
| Sequence | TODO |
| Tree | TODO |
| List | TODO |

### 3. Naming convention audit

Apply the naming conventions established for Map:

- **Optics** = past tense (`filtered`, `adjusted`, `mapped`)
- **Operators** = present tense or `*Of` pattern (`sortsOf`, `sortFoldOf`)
- **Constructors** = declarative/present participle (`setter`, `cosetter`, `adjoint`)
- `foo` wraps `Container.foo`, `ixfoo` wraps `Container.fooWithKey`
- No module-name suffixes (each module scopes its own names)
- No `->` in type variables
- No partial functions (`error`, `undefined`, `head`, `(!!)`)

| Module | Known violations |
|--------|----------------|
| IntMap | `foldSorts`/`foldSorts1`/`mconcatSorts` already renamed to `sortFoldOf`/`sortFold1Of`/`sortFoldMapOf`. Check for others. |
| IntMap | Lazy/strict tick variants — needs strict/lazy split like Map |
| Sequence | Check `grateSeq` → already renamed to `zipped` |
| List | `sortsOf`/`sortsDescOf`/`groupsOf`/`nubsOf`/`sortsString` — already renamed. Check for others. |
| Tree | Minimal API, likely clean |
| Set | Minimal API, likely clean |

### 4. Regularize setter surface: foo / ixfoo / cxfoo triples

For every containers `foo` / `fooWithKey` pair, provide:
- `foo :: Adjoint ...` wrapping `Container.foo`
- `ixfoo :: Ixadjoint ...` wrapping `Container.fooWithKey`
- `cxfoo :: Cxadjoint ...` wrapping `Container.fooWithKey`

This was done comprehensively for Map. Apply to others where the
containers API provides `*WithKey`/`*WithIndex` variants:

| Module | Has *WithKey? | Needs Adjoint upgrade? |
|--------|--------------|----------------------|
| IntMap | Yes (`mapWithKey`, `filterWithKey`, `adjustWithKey`, etc.) | YES — full treatment like Map |
| Sequence | `mapWithIndex`, `traverseWithIndex`, `foldlWithIndex` | YES — Ix/Cx forms |
| List | `zipWith [0..]` pattern | Partial — already has `ixmapped`/`cxmapped` |
| Tree | No `*WithKey` | No — non-indexed only |
| Set | No `*WithKey` (elements are keys) | No |
| IntSet | No `*WithKey` | No |

### 5. Remove bloat

- Remove `mapped = setter fmap` / `comapped = cosetter fmap` wherever
  they duplicate the core's `fmapped`. Already done for Map.
- Remove `fromIxfold`-style trivial one-liners.

| Module | Status |
|--------|--------|
| IntMap | Check for remaining bloat |
| Sequence | `mapped`/`comapped` already removed |
| Tree | `mapped`/`comapped` already removed |
| List | Uses `fmapped` re-export, `comapped` already removed |
| Set | Minimal, likely clean |
| IntSet | Minimal, likely clean |

### 6. Remove bottoms

Audit for `error`, `undefined`, `head`, partial pattern matches.
Replace with total alternatives (Maybe focus, default parameter,
bounds checking).

| Module | Known issues |
|--------|-------------|
| IntMap | `zippedIf` family — already fixed with Maybe focus |
| Sequence | Check `zipped` for bounds issues |
| List | `cxfolded` uses `(!!)` — documented O(n^2), suggest Seq |
| Tree | Likely clean |
| Set | `zipped` uses filter — likely clean |
| IntSet | `zipped` uses filter — likely clean |

### 7. Strict/lazy split

Map was split into `Data.Map.Optic` (strict) and
`Data.Map.Lazy.Optic` (lazy). Apply the same where applicable:

| Module | Needs split? |
|--------|-------------|
| IntMap | YES — `Data.IntMap.Strict` vs `Data.IntMap.Lazy` |
| Sequence | No (Seq has no strict/lazy distinction) |
| Tree | No |
| List | No |
| Set | No |
| IntSet | No |

### 8. Coverage analysis (new optics)

Map got 6 new optics from the coverage analysis (`posAt`,
`mappedIf`, `mappedKey`, `filtered`, `updatedMin`, `updatedMax`).
Do the same analysis for each container:

| Module | Potential new optics |
|--------|---------------------|
| IntMap | Mirror all Map optics: `posAt`, `mappedIf`, `mappedKey`, `filtered`, `updatedMin`/`Max` |
| Sequence | `posAt` (already have `at`), check for filter/mapMaybe gaps |
| List | Check for filter/take/drop gaps |
| Tree | Minimal — recursive structure limits optic surface |
| Set | `filtered` wrapping `Set.filter` |
| IntSet | `filtered` wrapping `IntSet.filter` |

### 9. Merge operators (IntMap only)

IntMap already has merge operators (`merges`, `mergesInner`, etc.).
Verify they match the Map rename:
- `mergesInner`/`mergesOuter`/`mergesLeft`/`mergesRight` (done)
- `sortsWhenMatched`/`sortsWhenMissing` (done)
- Use `SimpleWhenMissing`/`SimpleWhenMatched` newtypes (done)

### 10. Property tests

Add property tests for new optics. Follow the pattern from
`Test/Carrier.hs`:
- `id_adjoint` / `compose_adjoint` for Adjoint optics
- Roundtrip tests for `posAt`, `at`, etc.

### 11. Benchmarks

Add benchmarks for strict Map.Optic API:
- `adjusted` vs direct `Map.adjust`
- `filtered` vs direct `Map.filter`
- `ixmapped` vs direct `Map.mapWithKey`
- `updated` vs direct `Map.update`
- Sort operators vs direct

## Work order

Phase 1 — IntMap (largest, mirrors Map closely):
1. Strict/lazy split
2. Adjoint upgrade (Setter/Cosetter → Adjoint/Ixadjoint/Cxadjoint)
3. Coverage analysis + new optics
4. Naming audit
5. Property tests

Phase 2 — Sequence:
6. Diamond structure + Adjoint upgrade
7. Coverage analysis
8. Naming audit

Phase 3 — List:
9. Diamond structure + Adjoint upgrade
10. Naming audit

Phase 4 — Tree, Set, IntSet (small modules):
11. Diamond structure
12. Any remaining cleanup

Phase 5 — Benchmarks:
13. Map.Optic benchmarks
14. IntMap.Optic benchmarks

Phase 6 — Cross-cutting:
15. Final naming audit across all modules
16. Verify all modules have diamond blurb
17. Verify no bottoms anywhere
18. Verify all re-exports present

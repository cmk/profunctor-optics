# Sprint 21 — container-optics: dual optics + upstream migration

## Scope

Fill out the dual (Costar-side) optic surface for containers (Map,
IntMap, Set, IntSet, Seq, Tree, List), then migrate everything that
doesn't require extra dependencies from the satellite library into
the core `profunctor-optics` package. What stays in the satellite
(`container-optics`, renamed from `profunctor-optics-containers`) is
nonempty-containers variants and recursion-scheme-based operations.

## Rationale

The core library already has Map/IntMap/Set/IntSet/Seq/Tree/List optic
modules with full Star-side (Ix) coverage. But the Cx (coindexed) duals
are missing, and the Cotraversal/Cosetter surfaces are thin. Containers
is a boot library — no new dependencies needed to move everything
upstream.

## Module conventions

Each container optic module (e.g. `Data.Map.Optic`) must organize its
exports and source code in two sections:

1. **Optics** — optic definitions and constructors
2. **Operators** — functions that consume monomorphized optics (`view`,
   `set`, `over`, `cosets`, etc. applied to specific container optics)

Within each section, order functions by optic type following the
canonical ordering in `Data.Profunctor.Optic.Types`:

```
-- * Optics
-- ** Iso
-- ** Lens, Ixlens
-- ** Prism, Ixprism
-- ** Traversal, Ixtraversal
-- ** Traversal0, Ixtraversal0
-- ** Traversal1, Ixtraversal1
-- ** Fold, Ixfold
-- ** Fold0, Ixfold0
-- ** Fold1, Ixfold1
-- ** View, Ixview
-- ** Setter, Ixsetter
-- ** Setter1, Ixsetter1
-- ** Adjoint, Ixadjoint, Cxadjoint
-- ** Colens, Cxlens
-- ** Relens, Rxlens
-- ** Reprism, Rxprism
-- ** Cotraversal, Cxtraversal
-- ** Cotraversal0, Cxtraversal0
-- ** Cotraversal1, Cxtraversal1
-- ** Cofold, Cxfold
-- ** Cofold0, Cxfold0
-- ** Cofold1, Cxfold1
-- ** Coview, Cxview
-- ** Review
-- ** Cosetter, Cxsetter
-- ** Cosetter1, Cxsetter1
-- * Operators
-- (same ordering within)
```

Only include subsections for optic types that the module actually
defines. This ordering ensures consistency across all container optic
modules and makes it easy to find the dual of any optic.

## Phase 1 — Cx duals for Map/IntMap (S21.1–S21.6)

These fill the coindexed gap identified in the dual-optic-usecases analysis.

| ID | File | Task |
|----|------|------|
| S21.1 | Map/Optic.hs | `cxmapped :: Cxsetter k (Map k a) (Map k b) a b` — Cx dual of `ixmapped`, wraps `mapWithKey` |
| S21.2 | Map/Optic.hs | `cxfiltered :: Cxsetter k (Map k a) (Map k a) a Bool` — wraps `filterWithKey` |
| S21.3 | Map/Optic.hs | `cxmapMaybed :: Cxsetter k (Map k a) (Map k b) a (Maybe b)` — wraps `mapMaybeWithKey` |
| S21.4 | Map/Optic.hs | `cxfolded :: Cxfold k (Map k a) a` — Cx dual of `ixfolded`, wraps `foldMapWithKey` |
| S21.5 | Map/Optic.hs | `cxtraversed :: Cxtraversal k (Map k a) (Map k b) a b` — wraps `traverseWithKey` |
| S21.6 | IntMap/Optic.hs | Mirror S21.1–S21.5 for IntMap (same shapes, `Int` key) |

## Phase 2 — Cotraversal for Map/Seq (S21.7–S21.9)

Pointwise zipping as Cotraversals.

| ID | File | Task |
|----|------|------|
| S21.7 | Map/Optic.hs | `zippedMap :: Ord k => Set k -> Cotraversal (Map k a) (Map k b) a b` — pointwise cotraversal over a known key set (extends `zipsMap` from Colens to Cotraversal) |
| S21.8 | Sequence/Optic.hs | `zippedSeq :: Int -> Cotraversal (Seq a) (Seq b) a b` — pointwise cotraversal (extends `grateSeq`) |
| S21.9 | Map/Optic.hs | `cxzippedMap :: Ord k => Set k -> Cxcotraversal k (Map k a) (Map k b) a b` — keyed zip cotraversal using `Map.intersectionWithKey` |

## Phase 3 — Cosetter for accumulating operations (S21.10–S21.12)

Stateful transforms via `mapAccumWithKey`.

| ID | File | Task |
|----|------|------|
| S21.10 | Map/Optic.hs | Investigate `mapAccumWithKey` as a Cosetter with state threading — determine if this fits the Cosetter pattern or needs a new combinator |
| S21.11 | Sequence/Optic.hs | Investigate `Seq.mapWithIndex` as Cxsetter (Seq has no `mapAccum`) |
| S21.12 | List/Optic.hs | `cxmapped :: Cxsetter Int [a] [b] a b` — wraps indexed map for lists |

## Phase 4 — Tree dual optics (S21.13–S21.15)

| ID | File | Task |
|----|------|------|
| S21.13 | Tree/Optic.hs | `zipsTree :: Cotraversal (Tree a) (Tree b) a b` — pointwise zip of trees (deferred TODO in current Tree/Optic.hs; needs careful handling of mismatched subforest shapes) |
| S21.14 | Tree/Optic.hs | `unfoldedTree :: Colens (Tree a) (Tree b) (??? -> a) (??? -> b)` — investigate `unfoldTree :: (b -> (a, [b])) -> b -> Tree a` as a Colens/Grate |
| S21.15 | Tree/Optic.hs | `foldedTree :: Cosetter (Tree a) b a ([b] -> b)` — investigate `foldTree :: (a -> [b] -> b) -> Tree a -> b` as a Cosetter or Cofold |

## Phase 5 — Upstream migration (S21.16–S21.18)

Move container optics from the satellite library into `profunctor-optics` core.

| ID | Task |
|----|------|
| S21.16 | Move `Data.Map.Optic`, `Data.IntMap.Optic`, `Data.Set.Optic`, `Data.IntSet.Optic`, `Data.Sequence.Optic`, `Data.Tree.Optic`, `Data.List.Optic` from satellite to core (already partially there — reconcile duplicates). The core already depends on `containers`, so no new deps. |
| S21.17 | Move Sort-related container operations (`sorts`, `toMapOf`, `merges`, etc.) — these are already in the core Sort.hs but verify nothing's duplicated in the satellite. |
| S21.18 | Audit the satellite: after migration, only `Data.Map.NonEmpty.Optic`, `Data.Map.Fold.Optic`, `Data.Container.Pattern` should remain (these depend on `nonempty-containers` and `scheme-extensions`). Update the satellite cabal file accordingly. |

## Phase 6 — Properties and tests (S21.19–S21.21)

| ID | File | Task |
|----|------|------|
| S21.19 | Property.hs | Add property predicates for Cxsetter (`id_cxsetter`, `compose_cxsetter`) and Cxfold (`id_cxfold`) |
| S21.20 | Test/Carrier.hs | Hedgehog tests for new Cx container optics at `Conjoin ()` |
| S21.21 | Test/ | Hedgehog tests for new Cotraversal container optics (zip roundtrips) |

## Dependencies

- Sprint 20 (Adjoint types, `cosetter`/`cxsetter` generalization) — DONE
- `containers` is a boot library — no new deps for core

## Deliverables

- Full Cx coverage for Map/IntMap: `cxmapped`, `cxfiltered`, `cxmapMaybed`, `cxfolded`, `cxtraversed`
- Cotraversal zips for Map and Seq
- Tree dual optics (best-effort — recursive structure may need special handling)
- Clean satellite split: core has everything that depends only on `containers`; satellite has nonempty + recursion schemes

# Sprint 23 — vector-optics: dual optics for Vector

## Scope

Create a new `vector-optics` satellite library with full Star-side
AND Costar-side optic coverage for `Data.Vector.Generic`,
`Data.Vector`, `Data.Vector.Unboxed`, and `Data.Vector.Storable`.

## Rationale

Vector has the richest indexed API of any Haskell container —
every major operation has an `i`-prefixed variant (`imap`, `ifilter`,
`imapMaybe`, `ifoldl'`, `ifoldr`, `itraverse`, `iscanl'`, `izipWith`
up to 6-ary). It also has unique operations like `generate`,
`backpermute`, and `constructN` that don't exist in other containers.
Currently there is zero optic coverage for Vector.

## Module conventions

Follow the module conventions from Sprint 21: two sections (Optics,
Operators), ordered by optic type following the canonical ordering in
`Data.Profunctor.Optic.Types`. See Sprint 21 for the full ordering.

## Phase 1 — Package setup (S23.1)

| ID | Task |
|----|------|
| S23.1 | Create `vector-optics` package: cabal file, `Data.Vector.Optic` module, dependency on `profunctor-optics` + `vector`. Decide whether to target `Data.Vector.Generic` (polymorphic over vector type) or specialize to `Data.Vector` (boxed). Recommendation: Generic where possible, with boxed specializations. |

## Phase 2 — Star-side (Ix) optics (S23.2–S23.7)

The standard optic surface, mirroring what Map/Seq already have.

| ID | File | Task |
|----|------|------|
| S23.2 | Vector/Optic.hs | `at :: Int -> Traversal0' (v a) a` — element access by index (`v ! i` + `v // [(i, b)]`) |
| S23.3 | Vector/Optic.hs | `ixat :: Int -> Ixtraversal0' Int (v a) a` — indexed element access |
| S23.4 | Vector/Optic.hs | `ixtraversed :: Ixtraversal Int (v a) (v b) a b` — indexed traversal wrapping `itraverse` |
| S23.5 | Vector/Optic.hs | `ixmapped :: Ixsetter Int (v a) (v b) a b` — indexed setter wrapping `imap` |
| S23.6 | Vector/Optic.hs | `ixfolded :: Ixfold Int (v a) a` — indexed fold wrapping `ifoldr` |
| S23.7 | Vector/Optic.hs | `ixfiltered :: Ixsetter Int (v a) (v a) a Bool` — indexed filter wrapping `ifilter` |

## Phase 3 — Costar-side (Cx) duals (S23.8–S23.13)

The dual optics — the main value-add over a naive port.

| ID | File | Task |
|----|------|------|
| S23.8 | Vector/Optic.hs | `cxmapped :: Cxsetter Int (v a) (v b) a b` — Cx dual of `ixmapped`, wraps `imap` on the Costar side |
| S23.9 | Vector/Optic.hs | `cxfiltered :: Cxsetter Int (v a) (v a) a Bool` — wraps `ifilter` |
| S23.10 | Vector/Optic.hs | `cxmapMaybed :: Cxsetter Int (v a) (v b) a (Maybe b)` — wraps `imapMaybe` |
| S23.11 | Vector/Optic.hs | `cxfolded :: Cxfold Int (v a) a` — wraps `ifoldr`/`ifoldl'` on the Costar side |
| S23.12 | Vector/Optic.hs | `cxtraversed :: Cxtraversal Int (v a) (v b) a b` — wraps `itraverse` |
| S23.13 | Vector/Optic.hs | `cxscanned :: Cxsetter Int (v a) (v b) a b` — investigate `iscanl'`/`iscanr` as indexed Cxsetters |

## Phase 4 — Colens / Grate (S23.14–S23.17)

Vector-as-function optics.

| ID | File | Task |
|----|------|------|
| S23.14 | Vector/Optic.hs | `grateVec :: Int -> Colens (v a) (v b) (Int -> a) (Int -> b)` — views a vector as a function from indices, wraps `generate`/`(!)`. Same pattern as `zipsMap` / `grateSeq`. |
| S23.15 | Vector/Optic.hs | `backpermuted :: v Int -> Colens (v a) (v b) a b` — wraps `backpermute`. The permutation vector acts as the "key set" (like `Set k` in `zipsMap`). |
| S23.16 | Vector/Optic.hs | `slicedVec :: Int -> Int -> Colens (v a) (v b) (Int -> a) (Int -> b)` — Colens into a slice (offset + length), wraps `slice` + `generate` |
| S23.17 | Vector/Optic.hs | `constructed :: Int -> Colens (v a) (v a) (v a -> a) (v a -> a)` — investigate `constructN` as a self-referential Colens where each element sees the prefix. Novel shape. |

## Phase 5 — Cotraversal / zipping (S23.18–S23.21)

| ID | File | Task |
|----|------|------|
| S23.18 | Vector/Optic.hs | `zippedVec :: Int -> Cotraversal (v a) (v b) a b` — pointwise Cotraversal, wraps `zipWith` |
| S23.19 | Vector/Optic.hs | `cxzippedVec :: Int -> Cxcotraversal Int (v a) (v b) a b` — indexed zip via `izipWith` |
| S23.20 | Vector/Optic.hs | Investigate higher-arity zips (`zipWith3` through `zipWith6`, `izipWith3` through `izipWith6`) — determine if these fit the optic framework or are better left as raw functions |
| S23.21 | Vector/Optic.hs | `unzippedVec :: Iso (v (a, b)) (v (c, d)) (v a, v b) (v c, v d)` — `unzip`/`zip` as an Iso |

## Phase 6 — Sort integration (S23.22–S23.23)

| ID | File | Task |
|----|------|------|
| S23.22 | Vector/Optic.hs | `sortingVec :: Ord k => (a -> k) -> v a -> Map k (v a)` — Sort-based vector sorting using `sortingRep` with vector's `length`/`(!)` interface |
| S23.23 | Vector/Optic.hs | Investigate Sort pipeline composition for multi-key vector sorting (primary + secondary sort keys) |

## Phase 7 — Properties and tests (S23.24–S23.26)

| ID | File | Task |
|----|------|------|
| S23.24 | test/ | Hedgehog generators for Vector |
| S23.25 | test/ | Property tests for Star-side optics (Ix roundtrips, setter laws) |
| S23.26 | test/ | Property tests for Costar-side optics (Cx roundtrips, zip cotraversal laws) |

## Open questions

- **Generic vs specialized**: `Data.Vector.Generic` is polymorphic
  over the vector type via the `Vector v a` constraint. Optics should
  target this where possible, but some operations (e.g., `imapMaybe`)
  may require `Vector v a, Vector v b` which complicates the optic
  types. May need both generic and boxed-specialized variants.

- **constructN**: `constructN :: Int -> (v a -> a) -> v a` is unique
  to Vector. Each element is built from the prefix vector built so
  far. This is a coalgebraic/corecursive shape that doesn't fit
  standard optic types cleanly. May be best as a specialized
  combinator rather than a standard Colens.

- **Mutable vectors**: Vector's mutable API (`Data.Vector.Mutable`)
  has `modify`, `write`, `read` etc. in `ST`/`IO`. These could
  potentially be modeled as optics in a monadic context, but this
  is out of scope for this sprint.

## Dependencies

- Sprint 21 (Cx container optics — establishes the patterns)
- `vector` library

## Deliverables

- New `vector-optics` package with full Star + Costar optic coverage
- Ix optics: `at`, `ixtraversed`, `ixmapped`, `ixfolded`, `ixfiltered`
- Cx optics: `cxmapped`, `cxfiltered`, `cxmapMaybed`, `cxfolded`, `cxtraversed`
- Colens: `grateVec`, `backpermuted`
- Cotraversal: `zippedVec`, `cxzippedVec`
- Sort integration for vector sorting

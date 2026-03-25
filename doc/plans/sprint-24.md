# Sprint 24 — hashable-optics: dual optics for HashMap and HashSet

## Scope

Create a new `hashable-optics` satellite library with full Star-side
AND Costar-side optic coverage for `Data.HashMap.Strict`,
`Data.HashMap.Lazy`, and `Data.HashSet` from `unordered-containers`.

## Rationale

HashMap mirrors Map's API closely but with `(Eq k, Hashable k)`
constraints instead of `Ord k`. The library currently has zero optic
coverage for HashMap/HashSet. HashMap also has operations not in Map
(`compose`, `unionWithKey`, `intersectionWithKey`, `differenceWithKey`)
that map to Sort-based merge combinators.

## Module conventions

Follow the module conventions from Sprint 21: two sections (Optics,
Operators), ordered by optic type following the canonical ordering in
`Data.Profunctor.Optic.Types`. See Sprint 21 for the full ordering.

## Phase 1 — Package setup (S24.1)

| ID | Task |
|----|------|
| S24.1 | Create `hashable-optics` package: cabal file, `Data.HashMap.Optic` and `Data.HashSet.Optic` modules, dependency on `profunctor-optics` + `unordered-containers` + `hashable`. |

## Phase 2 — HashMap Star-side (Ix) optics (S24.2–S24.9)

Mirror the existing Map.Optic surface for HashMap.

| ID | File | Task |
|----|------|------|
| S24.2 | HashMap/Optic.hs | `at :: (Eq k, Hashable k) => k -> Traversal0' (HashMap k a) a` — wraps `lookup`/`insert`/`delete` |
| S24.3 | HashMap/Optic.hs | `ixat :: (Eq k, Hashable k) => k -> Ixtraversal0' k (HashMap k a) a` — indexed at |
| S24.4 | HashMap/Optic.hs | `ixtraversed :: Ixtraversal k (HashMap k a) (HashMap k b) a b` — wraps `traverseWithKey` |
| S24.5 | HashMap/Optic.hs | `ixmapped :: Ixsetter k (HashMap k a) (HashMap k b) a b` — wraps `mapWithKey` |
| S24.6 | HashMap/Optic.hs | `ixfolded :: Ixfold k (HashMap k a) a` — wraps `foldrWithKey` |
| S24.7 | HashMap/Optic.hs | `ixfiltered :: Ixsetter k (HashMap k a) (HashMap k a) a Bool` — wraps `filterWithKey` |
| S24.8 | HashMap/Optic.hs | `altered :: (Eq k, Hashable k) => k -> Setter' (HashMap k a) (Maybe a)` — wraps `alter` |
| S24.9 | HashMap/Optic.hs | `alteredF :: (Eq k, Hashable k) => k -> Lens' (HashMap k a) (Maybe a)` — wraps `alterF` |

## Phase 3 — HashMap Costar-side (Cx) duals (S24.10–S24.15)

| ID | File | Task |
|----|------|------|
| S24.10 | HashMap/Optic.hs | `cxmapped :: Cxsetter k (HashMap k a) (HashMap k b) a b` — wraps `mapWithKey` on the Costar side |
| S24.11 | HashMap/Optic.hs | `cxfiltered :: Cxsetter k (HashMap k a) (HashMap k a) a Bool` — wraps `filterWithKey` |
| S24.12 | HashMap/Optic.hs | `cxmapMaybed :: Cxsetter k (HashMap k a) (HashMap k b) a (Maybe b)` — wraps `mapMaybeWithKey` |
| S24.13 | HashMap/Optic.hs | `cxfolded :: Cxfold k (HashMap k a) a` — wraps `foldMapWithKey` |
| S24.14 | HashMap/Optic.hs | `cxtraversed :: Cxtraversal k (HashMap k a) (HashMap k b) a b` — wraps `traverseWithKey` |
| S24.15 | HashMap/Optic.hs | `cxmapped' :: Cxview k (HashMap k a -> HashMap k b) (a -> b)` — Cxview for keyed map, mirrors `cxmapped'` in Map.Optic |

## Phase 4 — Merge / binary operations (S24.16–S24.21)

HashMap's merge operations, wrapping `unionWithKey`,
`intersectionWithKey`, `differenceWithKey`.

| ID | File | Task |
|----|------|------|
| S24.16 | HashMap/Optic.hs | `innerMergesHash :: (Eq k, Hashable k) => (k -> a -> b -> c) -> HashMap k a -> HashMap k b -> HashMap k c` — wraps `intersectionWithKey` |
| S24.17 | HashMap/Optic.hs | `outerMergesHash :: (Eq k, Hashable k) => (k -> a -> c) -> (k -> b -> c) -> (k -> a -> b -> c) -> HashMap k a -> HashMap k b -> HashMap k c` — left+right+both merge, built from `unionWith` + `intersectionWithKey` + `differenceWith` |
| S24.18 | HashMap/Optic.hs | `leftMergesHash :: (Eq k, Hashable k) => (k -> a -> c) -> (k -> a -> b -> c) -> HashMap k a -> HashMap k b -> HashMap k c` — left merge |
| S24.19 | HashMap/Optic.hs | `rightMergesHash :: (Eq k, Hashable k) => (k -> b -> c) -> (k -> a -> b -> c) -> HashMap k a -> HashMap k b -> HashMap k c` — right merge |
| S24.20 | HashMap/Optic.hs | Investigate Sort-based merge integration: can `sortedMatched`/`sortedMissing` be generalized to work with HashMap, or do they fundamentally require `Ord k`? |
| S24.21 | HashMap/Optic.hs | `composed :: (Eq b, Hashable b) => Setter (HashMap a b, HashMap b c) (HashMap a b, HashMap a c) (HashMap b c) (HashMap a c)` — investigate `HashMap.compose` as an optic. This is relational composition: `(a -> b) . (b -> c) = (a -> c)` at the map level. |

## Phase 5 — HashSet optics (S24.22–S24.25)

| ID | File | Task |
|----|------|------|
| S24.22 | HashSet/Optic.hs | `member :: (Eq a, Hashable a) => a -> Fold0 (HashSet a) a` — membership test |
| S24.23 | HashSet/Optic.hs | `folded :: Fold (HashSet a) a` — fold over elements |
| S24.24 | HashSet/Optic.hs | `listed :: (Eq a, Hashable a) => Iso' (HashSet a) [a]` — iso to list (note: unordered) |
| S24.25 | HashSet/Optic.hs | `mapped :: (Eq b, Hashable b) => Setter (HashSet a) (HashSet b) a b` — wraps `HashSet.map` |

## Phase 6 — Colens (S24.26)

| ID | File | Task |
|----|------|------|
| S24.26 | HashMap/Optic.hs | Investigate whether `zipsMap`-style Colens is possible for HashMap. Unlike Map, HashMap doesn't have `fromSet` directly, but `HashMap.fromList` + `HashSet.toList` provides a path. The lack of ordering means the "function-from-keys" view is less natural. |

## Phase 7 — Properties and tests (S24.27–S24.29)

| ID | File | Task |
|----|------|------|
| S24.27 | test/ | Hedgehog generators for HashMap and HashSet |
| S24.28 | test/ | Property tests for Star-side optics (at roundtrips, setter laws) |
| S24.29 | test/ | Property tests for Costar-side optics (Cx roundtrips, merge properties) |

## Open questions

- **Sort integration**: The existing Sort-based merge combinators
  (`merges`, `innerMerges`, etc.) use `Map.Merge.Strict` which
  requires `Ord k`. HashMap's merge operations don't have the same
  structured `WhenMissing`/`WhenMatched` tactic API — they use
  simpler `unionWithKey`/`intersectionWithKey` signatures. The Sort
  integration may need to be different: simpler merge combinators
  that don't go through the tactic pattern.

- **Ordering**: HashMap is unordered. Operations like `foldlWithKey'`
  traverse in an unspecified order. This doesn't affect correctness
  of optics but means fold order is not deterministic. Document this
  in the optic haddocks.

- **HashSet vs Set**: HashSet has a much smaller API than Set (no
  merge tactics, no min/max). The optic surface will be correspondingly
  smaller.

- **HashMap.compose**: `compose :: Hashable b => HashMap b c -> HashMap a b -> HashMap a c`
  is unique to HashMap. It's relational composition at the map level.
  Whether this fits as a standard optic or is better left as a raw
  function needs investigation.

## Dependencies

- Sprint 21 (Cx container optics — establishes patterns)
- `unordered-containers`, `hashable`

## Deliverables

- New `hashable-optics` package
- Full Ix surface for HashMap: `at`, `ixtraversed`, `ixmapped`, `ixfolded`, `ixfiltered`, `altered`, `alteredF`
- Full Cx surface for HashMap: `cxmapped`, `cxfiltered`, `cxmapMaybed`, `cxfolded`, `cxtraversed`
- Merge combinators: `innerMergesHash`, `outerMergesHash`, `leftMergesHash`, `rightMergesHash`
- HashSet basics: `member`, `folded`, `listed`, `mapped`

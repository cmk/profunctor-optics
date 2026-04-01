# Sprint 28 — HashMap and HashSet optics

## Goal

New modules `Data.HashMap.Optic` (strict), `Data.HashMap.Lazy.Optic` (lazy),
and `Data.HashSet.Optic` providing profunctor optics for unordered-containers.

Mechanical port of the Map/Map.Lazy/Set optic modules, replacing `Ord k`
with `Hashable k` (and `Eq k` where the upstream API only needs equality).

## Module structure

```
profunctor-optics/src/
  Data/HashMap/Optic.hs         -- strict
  Data/HashMap/Lazy/Optic.hs    -- lazy (same exports, lazy semantics)
  Data/HashSet/Optic.hs
```

Or as a separate package `unordered-optics` — TBD based on dependency preferences.

## HashMap optic mapping

### Iso

| Name | Type | Upstream |
|------|------|----------|
| `packed` | `Iso' [(k, v)] (HashMap k v)` | `fromList`/`toList` |

No `reversed` (unordered). No `short` (no compact variant).

### Traversal0

| Name | Type | Upstream |
|------|------|----------|
| `at` | `Hashable k => k -> Traversal0' (HashMap k v) v` | `lookup`/`insert` |

### Lens

| Name | Type | Upstream |
|------|------|----------|
| `alteredF` | `(Hashable k, Functor f) => k -> Lens' (HashMap k v) (Maybe v)` | `alterF` |

### Traversal

| Name | Type | Upstream |
|------|------|----------|
| `ixtraversed` | `(Eq k, Hashable k, Semigroup k) => Ixtraversal k (HashMap k a) (HashMap k b) a b` | `traverseWithKey` |

### Fold

| Name | Type | Upstream |
|------|------|----------|
| `folded` | `Fold (HashMap k v) v` | via Foldable |
| `ixfolded` | `Semigroup k => Ixfold k (HashMap k v) v` | `foldrWithKey`/`foldMapWithKey` |

### Setter

| Name | Type | Upstream |
|------|------|----------|
| `mapped` | `Setter (HashMap k a) (HashMap k b) a b` | `map` |
| `ixmapped` | `Semigroup k => Ixadjoint k (HashMap k a) (HashMap k b) a b` | `mapWithKey` |
| `mappedKeys` | `Hashable k2 => Adjoint (HashMap k1 v) (HashMap k2 v) k1 k2` | `mapKeys` |

### Ixlens

| Name | Type | Upstream |
|------|------|----------|
| `ixalteredF` | `(Hashable k) => Ixlens' k (HashMap k v) (Maybe v)` | incoming index = key, `alterF` |
| `ixat` | `(Hashable k) => Ixtraversal0' k (HashMap k v) v` | incoming index = key, `lookup`/`insert` |

### Ixsetter / Ixadjoint

| Name | Type | Upstream |
|------|------|----------|
| `ixadjusted` | `Hashable k => Ixadjoint' k (HashMap k v) v` | incoming index = key, `adjust` |
| `ixaltered` | `Hashable k => Ixadjoint' k (HashMap k v) (Maybe v)` | incoming index = key, `alter` |
| `ixupdated` | `Hashable k => Ixadjoint k (HashMap k v) (HashMap k v) v (Maybe v)` | incoming index = key, `update` |
| `ixfiltered` | `Semigroup k => Ixadjoint k (HashMap k v) (HashMap k v) v Bool` | `filterWithKey` |
| `mappedMaybe` | `Semigroup k => Ixadjoint k (HashMap k a) (HashMap k b) a (Maybe b)` | `mapMaybeWithKey` |

### Adjoint

| Name | Type | Upstream |
|------|------|----------|
| `filtered` | `Adjoint (HashMap k v) (HashMap k v) v Bool` | `filter` |
| `sorted` | — | N/A (unordered) |

### Coindexed optics

| Name | Type | Upstream |
|------|------|----------|
| `cxtraversed` | `(Eq k, Hashable k, Semigroup k) => Cxtraversal k (HashMap k a) (HashMap k b) a b` | dual of `ixtraversed` |
| `cxfolded` | `(Eq k, Semigroup k) => Cxfold k (HashMap k v) v` | dual of `ixfolded` |
| `cxmapped` | `Semigroup k => Cxadjoint k (HashMap k a) (HashMap k b) a b` | dual of `ixmapped` |
| `cxfiltered` | `Semigroup k => Cxadjoint k (HashMap k v) (HashMap k v) v Bool` | dual of `ixfiltered` |
| `cxadjusted` | `Hashable k => Cxadjoint' k (HashMap k v) v` | dual of `ixadjusted` |
| `cxaltered` | `Hashable k => Cxadjoint' k (HashMap k v) (Maybe v)` | dual of `ixaltered` |
| `cxupdated` | `Hashable k => Cxadjoint k (HashMap k v) (HashMap k v) v (Maybe v)` | dual of `ixupdated` |

### Not included (no ordered operations)

- `lookedMin`/`lookedMax` (no ordering)
- `lookedLT`/`lookedLE`/`lookedGE`/`lookedGT` (no ordering)
- `updatedMin`/`updatedMax` (no ordering)
- `posAt` (no positional rank)
- `sorted` (unordered)
- `reversed` (unordered)

## HashSet optic mapping

HashSet is small — no key/value distinction, no indexed operations
(elements ARE the keys). Mirrors `Data.Set.Optic` with `Hashable`
instead of `Ord`.

### Iso

| Name | Type | Upstream |
|------|------|----------|
| `packed` | `Hashable a => Iso' [a] (HashSet a)` | `fromList`/`toList` |
| `mapped'` | `Iso' (HashMap k ()) (HashSet k)` | `fromMap`/`toMap` |

### Traversal0

| Name | Type | Upstream |
|------|------|----------|
| `contains` | `Hashable a => a -> Traversal0' (HashSet a) a` | `member`/`insert`/`delete` |

`contains k` focuses on element `k` if present. Setting inserts,
unsetting deletes. No indexed version — there's no separate key/value
to thread.

### Fold

| Name | Type | Upstream |
|------|------|----------|
| `folded` | `Fold (HashSet a) a` | via Foldable |

### Setter

| Name | Type | Upstream |
|------|------|----------|
| `mapped` | `Hashable b => Setter (HashSet a) (HashSet b) a b` | `HS.map` |

### Adjoint

| Name | Type | Upstream |
|------|------|----------|
| `filtered` | `Adjoint (HashSet a) (HashSet a) a Bool` | `HS.filter` |

### Not included

- No indexed/coindexed optics (elements are keys, no separate index)
- No ordering operations
- No `traversed` (HashSet is not Traversable — `map` can collapse duplicates)

## Implementation approach

Mechanical port of Map.Optic / Map.Lazy.Optic:

1. Copy Map.Optic, replace `Map.Map k` with `HashMap k`, `Ord k` with
   `Hashable k` (or `Eq k` where sufficient)
2. Replace `qualified Data.Map.Strict as Map` with
   `qualified Data.HashMap.Strict as HM`
3. Adjust function names where they differ:
   - `Map.traverseWithKey` → `HM.traverseWithKey` (same)
   - `Map.mapWithKey` → `HM.mapWithKey` (same)
   - `Map.filterWithKey` → `HM.filterWithKey` (same)
   - `Map.mapMaybeWithKey` → `HM.mapMaybeWithKey` (same)
   - `Map.adjustWithKey` → no WithKey variant; use `HM.adjust`
   - `Map.updateWithKey` → no WithKey variant; use `HM.update`
   - `Map.findWithDefault` → `HM.findWithDefault` (same)
   - `Map.insert` → `HM.insert` (same)
   - `Map.keysSet` → `HM.keysSet` (returns HashSet)
4. Remove ordered operations (looked*, updated*, posAt, sorted)
5. For `cxtraversed`/`cxfolded`: use `HM.mapWithKey` + `findWithDefault`
   pattern (same as Map, with total fallback from copure)
6. Lazy module: same exports, swap `Data.HashMap.Strict` for
   `Data.HashMap.Lazy`

### Constraint differences from Map

| Map | HashMap | Notes |
|-----|---------|-------|
| `Ord k` | `Hashable k` | For lookup/insert/delete |
| `Ord k` | `Eq k` | For union/intersection/traverseWithKey |
| `Semigroup k` | `Semigroup k` | For index accumulation (same) |

Some optics need both `Hashable k` AND `Semigroup k` (e.g., `ixtraversed`
which does lookup + accumulation).

### Key API differences from Map

- `HM.adjust :: Hashable k => (v -> v) -> k -> HashMap k v -> HashMap k v`
  (no `adjustWithKey` — use `adjust` + incoming index directly)
- `HM.update :: Hashable k => (a -> Maybe a) -> k -> HashMap k a -> HashMap k a`
  (no `updateWithKey` — use `update` + incoming index directly)
- No `Map.updateLookupWithKey` equivalent (good — we removed those)
- `HM.mapKeys :: Hashable k2 => (k1 -> k2) -> HashMap k1 v -> HashMap k2 v`
  (same as Map)

## Property testing

Same patterns as Map tests:

```haskell
-- ixtraversed agrees with traverseWithKey
prop_ixtraversed_eq m =
  ixsets ixtraversed (\k v -> ...) m == HM.mapWithKey (\k v -> ...) m

-- ixat at incoming index
prop_ixat_lookup m =
  ixpreview ixat m == ...

-- filtered agrees with HM.filter
prop_filtered_eq p m =
  sets filtered p m == HM.filter p m

-- mappedMaybe agrees with HM.mapMaybeWithKey
prop_mappedMaybe_eq f m =
  ixsets mappedMaybe f m == HM.mapMaybeWithKey (\k -> f k) m
```

## Ordering

1. **Phase 1**: HashMap.Optic (strict) — port from Map.Optic
2. **Phase 2**: HashMap.Lazy.Optic — swap imports
3. **Phase 3**: HashSet.Optic
4. **Phase 4**: Property tests

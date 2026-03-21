# Sprint 15 — Fill out containers API

## Scope

Replicate the Map optic pattern for all containers types: lazy Map,
strict/lazy Set, strict/lazy IntMap, IntSet. Strict and lazy
variants share the same module, with strict variants ticked (`'`).

## Module layout

| Module | Types | Variants |
|---|---|---|
| `Data.Map.Optic` | `Map.Map k a` | strict `at`, `imapped` etc. + lazy `at'` etc. |
| `Data.Set.Optic` | `Set.Set a` | `member`, `inserted`, `deleted`, `ifolded` |
| `Data.IntMap.Optic` | `IntMap.IntMap a` | strict `at`, `imapped` etc. + lazy `at'` etc. |
| `Data.IntSet.Optic` | `IntSet.IntSet` | `member`, `inserted`, `deleted`, `folded` |
| `Data.List.Optic` | `[a]` | (already done) |
| `Data.Sequence.Optic` | `Seq a` | (already done) |
| `Data.Tree.Optic` | `Tree a` | (already done) |

## Naming convention

Unprimed variants are lazy (matching `Data.Map.Lazy`). Primed
(`'`) variants are strict (matching `Data.Map.Strict`):

```haskell
-- Data.Map.Optic
at      :: Ord k => k -> Traversal0' (Map k a) a       -- strict
at'     :: Ord k => k -> Traversal0' (Map k a) a       -- lazy (same type, different semantics)
altered :: Ord k => k -> Setter' (Map k a) (Maybe a)    -- strict (Map.Strict.alter)
altered':: Ord k => k -> Setter' (Map k a) (Maybe a)    -- lazy (Map.Lazy.alter)
```

In practice most optics (at, itraversed, ifolded, values, etc.)
are the same for strict and lazy — the difference is only in
setters/alterations that insert new values. So many functions
won't need a lazy variant.

## Stories

| ID     | Module | Description |
|--------|--------|-------------|
| S15.1  | Data.Map.Optic | Add lazy variants where semantics differ |
| S15.2  | Data.Set.Optic | New module: Set optics |
| S15.3  | Data.IntMap.Optic | New module: IntMap optics (strict + lazy) |
| S15.4  | Data.IntSet.Optic | New module: IntSet optics |
| S15.5  | Data.Map.Optic | Sort-based operators for Map (toMapOfL etc. already done) |
| S15.6  | Data.IntMap.Optic | Sort-based operators for IntMap |
| S15.7  | Tests | Parallel test modules for each |

## S15.2 — Data.Set.Optic

```haskell
module Data.Set.Optic (
    -- * Membership
    member          -- :: Ord a => a -> Fold0 (Set a) a
    -- * Construction via optic
  , inserted        -- :: Ord a => a -> Setter' (Set a) Bool
  , deleted         -- :: Ord a => a -> Setter' (Set a) Bool
    -- * Fold
  , folded          -- :: Fold (Set a) a
  , ifolded         -- :: Ixfold Int (Set a) a  (positional)
    -- * Conversion
  , listed          -- :: Iso' (Set a) [a]  (via toAscList/fromList)
    -- * Sort-based
  , sortingSetL     -- :: Ord k => (a -> k) -> [a] -> Set a
) where
```

## S15.3 — Data.IntMap.Optic

Mirror Data.Map.Optic but with `Int` keys (no `Ord` constraint):

```haskell
module Data.IntMap.Optic (
    at, iat, values
  , imapped, ifiltered, itraversed, ifolded
  , altered, ialtered, alteredF, ialteredF
  , adjusted, updated, updateLooked
  , lookedMin, lookedMax, lookedLT, lookedLE, lookedGE, lookedGT
  , validated
    -- * Sort-based
  , toIntMapOfL, countingIntMapOfL
  , mergingIntMapOfL, innerMergeIntMapL
    -- * Sort merge tactics
  , sortedMatchedIntMap, sortedMissingIntMap
) where
```

## S15.4 — Data.IntSet.Optic

```haskell
module Data.IntSet.Optic (
    member
  , inserted, deleted
  , folded
  , listed
) where
```

## S15.1 — Lazy variants in Data.Map.Optic

Most optics are the same for strict and lazy. The difference is
only in setters that insert:

```haskell
-- These need lazy variants:
altered'  :: Ord k => k -> Setter' (Map k a) (Maybe a)  -- Map.Lazy.alter
ialtered' :: Ord k => k -> Ixsetter' k (Map k a) (Maybe a)

-- These are the same for both (reads don't differ):
-- at, iat, values, itraversed, ifolded, alteredF, ialteredF,
-- adjusted, updated, updateLooked, lookedMin/Max/LT/LE/GE/GT,
-- validated, toMapOfL, countingOfL, mergingOfL, etc.
```

## Hedgehog properties

| Prop | Module | Description |
|---|---|---|
| S1 | Set | `member` finds inserted element |
| S2 | Set | `folded` collects all elements |
| S3 | Set | `listed` roundtrip |
| S4 | IntMap | `at` get/set roundtrip |
| S5 | IntMap | `values` count = size |
| S6 | IntMap | `itraversed` identity |
| S7 | IntMap | `validated` passes for valid maps |
| S8 | IntSet | `member` finds inserted element |
| S9 | IntSet | `folded` collects all elements |

## Work order

1. S15.2 — Data.Set.Optic + tests
2. S15.3 — Data.IntMap.Optic + tests
3. S15.4 — Data.IntSet.Optic + tests
4. S15.1 — Lazy variants in Map.Optic
5. S15.5 — Sort-based operators for Map (verify existing)
6. S15.6 — Sort-based operators for IntMap
7. Green all properties

## Key files

- `profunctor-optics/src/Data/Set/Optic.hs` — new
- `profunctor-optics/src/Data/IntMap/Optic.hs` — new
- `profunctor-optics/src/Data/IntSet/Optic.hs` — new
- `profunctor-optics/src/Data/Map/Optic.hs` — add lazy variants
- `profunctor-optics/test/Test/Data/Set/Optic.hs` — new
- `profunctor-optics/test/Test/Data/IntMap/Optic.hs` — new
- `profunctor-optics/test/Test/Data/IntSet/Optic.hs` — new

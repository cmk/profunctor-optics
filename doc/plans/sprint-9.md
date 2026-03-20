# Sprint 9 — List/String variants and upstream tracing

## Scope

Add List and String (or IsString) variants of existing operators
where the NonEmpty/Text/ByteString versions are too specific.
Trace which Sort operators can move upstream into profunctor-optics
without adding new dependencies (no containers, vector, hashable,
bytestring, text).

## Rationale

Many Sort operators only need the core profunctor-optics types
(Lens, Colens, Cotraversal) plus base-library types (List, String,
Map). These can live in profunctor-optics proper, making them
available without the sort-specific package.

## Stories

| ID    | Module / target               | Description                                     |
|-------|-------------------------------|-------------------------------------------------|
| S9.1  | profunctor-optics             | List variants of Sort1 operators                |
| S9.2  | profunctor-optics             | String/IsString variants where possible         |
| S9.3  | doc/designs                   | Dependency trace: what can go upstream?          |
| S9.4  | profunctor-optics             | Move upstream-safe operators                    |
| S9.5  | Tests                         | Properties for new variants                     |

## S9.1 — List variants

Sort1 operators use NonEmpty. List variants accept `[s]` and
return `[[s]]` (or `Map k [s]`):

```haskell
-- Existing (NonEmpty):
sortingOf :: Ord a => Lens' s a -> NonEmpty s -> [NonEmpty s]

-- New (List, returns [] on empty input):
sortingOfL :: Ord a => Lens' s a -> [s] -> [[s]]
groupingOfL :: Ord a => Lens' s a -> [s] -> [[s]]
nubbingOfL :: Ord a => Lens' s a -> [s] -> [s]
toMapOfL :: Ord a => Lens' s a -> [s] -> Map a [s]
countingOfL :: Ord a => Lens' s a -> [s] -> Map a Int
```

## S9.2 — String/IsString variants

```haskell
-- Existing:
sortingBytes :: Ord k => (Word8 -> k) -> ByteString -> Map k ByteString
sortingChars :: Ord k => (Char -> k) -> Text -> Map k Text

-- New (String = [Char]):
sortingString :: Ord k => (Char -> k) -> String -> Map k String

-- Or via IsString (if overhead is acceptable):
sortingIsString :: (IsString s, ...) => ...
-- Probably not worth it — IsString doesn't give index/length.
-- Stick to concrete String.
```

## S9.3 — Dependency trace

Operators that need ONLY profunctor-optics + base + containers:

| Operator | Deps needed | Can upstream? |
|---|---|---|
| Sort type + instances | profunctors, coapplicative, transformers | YES (sprint 8) |
| `(%.)`, `bindSort`, `catSort` | Sort only | YES |
| `sortF`, `remapSort` | Sort only | YES |
| `eitherSort`, `maybeSort` | Sort + Monoid i | YES |
| `mkSort`, `mkSortN` | Sort + containers (Map) | YES (already a dep) |
| `sortingOfL` etc | Sort + Lens' + containers | YES |
| `mergingOf` etc | Sort + containers + Map.Merge | YES |
| `sortingRep` | Sort + containers | YES |
| `zipsSortingF` | Sort only | YES |
| `sortedMatchedF/MissingF` | Sort + containers (Map.Merge) | YES |
| `sortingVectorF` | vector | NO — stays in sort |
| `sortingBytes` | bytestring | NO — stays in sort |
| `sortingChars` | text | NO — stays in sort |
| `groupingHashOf` etc | hashable, unordered-containers | NO — stays in sort |
| `sortTaggedRep` etc | Sort + containers | YES |
| Sort1/Sort2 types | profunctors, coapplicative | MAYBE — could upstream |

## S9.4 — What moves upstream

Into profunctor-optics core (Carrier.hs or new Sort module):
- Sort type, instances, runSort, Category
- `(%.)`, bindSort, catSort, sortF, remapSort
- eitherSort, maybeSort
- mkSort, mkSortN (containers is already a profunctor-optics dep? check)

Into Optic/Lens.hs or a new Optic/Sort.hs in core:
- sortingOfL, groupingOfL, nubbingOfL, toMapOfL, countingOfL
- sortingRep, sortUniqueRep, sortTaggedRep, groupTaggedRep
- mergingOf, innerMerge, outerMerge, leftMerge, rightMerge
- sortedMatchedF, sortedMissingF

Stays in profunctor-optics-sort:
- Sort1, Sort2 (list-based carriers with hand-rolled instances)
- sortingVectorF, sortingBytes, sortingChars, sortingPrimArray, sortingArray
- Hashable operators
- All Sort1/Sort2-specific operators

## Key files

- `profunctor-optics/profunctor-optics.cabal` — check dep on containers
- `profunctor-optics/src/Data/Profunctor/Optic/Carrier.hs`
- `profunctor-optics/src/Data/Profunctor/Optic/Lens.hs` — zipsWith is here

# Dependency trace: what can go upstream?

## profunctor-optics current deps

```
base, adjunctions, coapplicative, distributive, mtl,
tagged, profunctors, semigroupoids, transformers
```

Notably absent: `containers`, `vector`, `bytestring`, `text`,
`hashable`, `unordered-containers`.

## What's already upstream (sprint 8-9)

| Function | Dep needed | Status |
|---|---|---|
| Sort type + instances | transformers (Compose), coapplicative | **Done** |
| `(%.)`, `bindSort`, `catSort` | Sort only | **Done** |
| `sortC`, `remapSort` | Sort only | **Done** |
| `eitherSort`, `maybeSort` | Sort + coapplicative | **Done** |
| `zipsSorting` | Sort only | **Done** |
| `runSort` | Sort only | **Done** |

## What could go upstream with containers

Adding `containers` (a boot library, ~zero cost) would unlock:

| Function | Additional dep | Value |
|---|---|---|
| `mkSort`, `mkSortN` | containers (Map) | Core carriers |
| `sortingOfL`, `groupingOfL`, `nubbingOfL` | containers (Map) | List-based sort operators |
| `toMapOfL`, `countingOfL` | containers (Map) | Container construction |
| `sortingRep`, `sortUniqueRep` | containers (Map) | Generic representable sort |
| `sortTaggedRep`, `groupTaggedRep` | containers (Map) | Tagged sort |
| `mergingOf`, `innerMerge`, `outerMerge` | containers (Map, Map.Merge) | Merge pipeline |
| `sortedMatched`, `sortedMissing` | containers (Map.Merge) | Sort as merge tactics |
| `foldSorting`, `mconcatSorting` | containers (indirect via Sort1) | Post-sort folds |
| `sortingString` | containers (Map) | String sort |

## What stays downstream (needs non-boot deps)

| Function | Dep | Package |
|---|---|---|
| `sortingVector`, `sortingVectorU` | vector | profunctor-optics-sort |
| `sortingPrimArray` | primitive | profunctor-optics-sort |
| `sortingArray` | array | profunctor-optics-sort |
| `sortingBytes`, `groupingBytes` | bytestring | profunctor-optics-sort |
| `sortingChars` | text | profunctor-optics-sort |
| `mkSortH`, `mkSortNH` | hashable | profunctor-optics-sort |
| `sortingRepH`, `groupingHashOf` etc | hashable + unordered-containers | profunctor-optics-sort |
| Sort1/Sort2 types | coapplicative (already a dep) | could upstream |

## Recommendation

Add `containers` to profunctor-optics. It's a boot library with
zero transitive cost. This unlocks the full Sort operator
vocabulary in core, making profunctor-optics self-contained for
the common case (sort/group/merge with Ord keys on lists).

The downstream package (profunctor-optics-sort) retains only
backend-specific operators (Vector, PrimArray, Array, ByteString,
Text, HashMap) that need non-boot deps.

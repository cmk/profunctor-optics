# Sprint 6 — Vector, primitive array, array, and hashable optics

## Scope

Prototype profunctor optics and Sort operators for the three
array-like container libraries (`vector`, `primitive`, `array`)
and the `hashable` library. The array types are Int-indexed
(or Ix-indexed) representable types, making them natural Sort3
carriers via `mkSort3N`. Hashable provides an alternative
discrimination key to `Ord`, enabling unordered grouping.

## Rationale

Vector, PrimArray, and Array are the workhorses of Haskell array
computation. All three are representable by their index type
(`Int` for vector/primitive, `Ix i => i` for array), which maps
directly to Sort3's `(i -> (k, a))` input. The `generate` family
(`V.generate`, `generatePrimArray`, `genArray`) witnesses the
isomorphism in each case.

The existing `profunctor-optics-sequences` uses `mono-traversable`
as its abstraction layer, which adds a dependency and isn't
profunctor-native. This sprint prototypes direct optics for
each backend to see whether a leaner approach works better.

## Stories

| ID    | Module / target                  | Description                                        |
|-------|----------------------------------|----------------------------------------------------|
| S6.1  | Data.Vector.Optic                | Boxed Vector optics: isos, cotraversals, Sort3 ops |
| S6.2  | Data.Vector.Unboxed.Optic        | Unboxed Vector optics (Unbox constraint)            |
| S6.3  | Data.Primitive.Array.Optic       | PrimArray optics (Prim constraint)                  |
| S6.4  | Data.Array.Optic                 | Array optics (Ix-indexed, multi-dimensional)        |
| S6.5  | Data.Profunctor.Optic.Sort       | Generic sortingArray for any generate/index pair    |
| S6.6  | Data.Profunctor.Sort / Optic.Sort| Hashable-keyed grouping (unordered discrimination)  |
| S6.7  | Test.Prop.Array                  | Hedgehog properties                                 |

## Key design decisions

### Representability witnesses

Each type has a `generate`/`index` pair that witnesses representability:

```
Vector:   generate :: Int -> (Int -> a) -> Vector a
          (!)      :: Vector a -> Int -> a

PrimArray: generatePrimArray :: Prim a => Int -> (Int -> a) -> PrimArray a
           indexPrimArray     :: Prim a => PrimArray a -> Int -> a

Array:    genArray :: Ix i => (i,i) -> (i -> e) -> Array i e
          (!)      :: Ix i => Array i e -> i -> e
```

These map to Sort3's input/output:
- Input: `i -> (k, a)` ≅ `index container i` with key extraction
- Output: `j -> k -> b` materialized via `generate`

### Array's Ix parameter

`Array i e` uses `Ix i` instead of raw `Int`. This is interesting
for Sort3 because `i` could be multi-dimensional: `(Int, Int)` for
matrices, `(Int, Int, Int)` for 3D arrays. A `mkSort3Ix` variant
would enumerate `range (lo, hi)` instead of `[0..n-1]`.

### Unboxed constraints

`Vector.Unboxed` requires `Unbox a`, `PrimArray` requires `Prim a`.
Sort3 carriers are polymorphic in `a`, so the constraint only matters
at the materialization boundary (when building the output container).

## New functions

### S6.1 — Boxed Vector optics

```haskell
-- | Iso between Vector and its generate/index representation.
vectored :: Iso' (V.Vector a) (Int, Int -> a)
-- or more precisely:
vectorRep :: V.Vector a -> (Int, Int -> a)
vectorRep v = (V.length v, (v V.!))

fromVectorRep :: (Int, Int -> a) -> V.Vector a
fromVectorRep (n, f) = V.generate n f

-- | Colens: Vector as representable container.
vectorGrate :: Colens (V.Vector a) (V.Vector b) (Int -> a) (Int -> b)

-- | Sort a Vector by key, producing Map of Vectors (already done).
sortingVector :: Ord k => (a -> k) -> V.Vector a -> Map k (V.Vector a)

-- | Sort a Vector by key via a Lens on elements.
sortingVectorOf :: Ord k => Lens' a k -> V.Vector a -> Map k (V.Vector a)

-- | Group-by on a Vector, returning groups as Vectors.
groupingVector :: Ord k => (a -> k) -> V.Vector a -> Map k (V.Vector a)

-- | Indexed map over Vector via Sort3 grouping.
imapSorted :: Ord k => (a -> k) -> (k -> a -> b) -> V.Vector a -> V.Vector b
```

### S6.2 — Unboxed Vector optics

```haskell
-- | Same as boxed but with Unbox constraints.
sortingVectorU :: (VU.Unbox a, VU.Unbox k, Ord k)
               => (a -> k) -> VU.Vector a -> Map k (VU.Vector a)
```

### S6.3 — PrimArray optics

```haskell
-- | Sort a PrimArray by key.
sortingPrimArray :: (Prim a, Ord k)
                 => (a -> k) -> PrimArray a -> Map k (PrimArray a)

-- | Colens: PrimArray as representable container.
primArrayGrate :: Prim a => Colens (PrimArray a) (PrimArray b) (Int -> a) (Int -> b)
```

### S6.4 — Array optics

```haskell
-- | Ix-aware Sort3 carrier.
mkSort3Ix :: (Ix i, Ord k) => (i, i) -> Sort3 i Int k a a

-- | Sort an Array by key, preserving Ix structure.
sortingArray :: (Ix i, Ord k)
             => (e -> k) -> Array i e -> Map k [(i, e)]

-- | Colens: Array as Ix-representable container.
arrayGrate :: Ix i => (i, i) -> Colens (Array i e) (Array i e') (i -> e) (i -> e')
```

### S6.5 — Generic sorting for representable containers

```haskell
-- | Sort any representable container given generate/index/length.
sortingRep :: Ord k
           => (c -> Int)          -- length
           -> (c -> Int -> a)     -- index
           -> (Int -> (Int -> b) -> c')  -- generate
           -> (a -> k)            -- key
           -> c -> Map k c'
```

### S6.6 — Hashable-keyed grouping

`Hashable` provides O(1) average-case discrimination via hashing,
complementing `Ord`'s O(log n) tree-based discrimination. The
discrimination library uses `hashing :: Hashable a => Group a`
for this. For Sort, the key insight is: where `Ord k` gives
sorted groups (Map), `Hashable k` gives unsorted groups (HashMap).

```haskell
-- | Sort1 carrier using Hashable instead of Ord.
-- Groups by hash, producing a HashMap of groups.
mkSort1H :: Hashable k => Sort1 k a a

-- | Group by Hashable key through a lens.
groupingHashOf :: Hashable a
               => Lens' s a
               -> NonEmpty s -> HashMap a (NonEmpty s)

-- | Unordered toMap via Hashable.
toHashMapOf :: Hashable a
            => Lens' s a
            -> NonEmpty s -> HashMap a (NonEmpty s)

-- | Count occurrences per Hashable key.
countingHashOf :: Hashable a
               => Lens' s a
               -> NonEmpty s -> HashMap a Int

-- | Merge two collections via Hashable keys.
-- Note: unordered-containers has no WhenMatched/WhenMissing merge API.
-- Use unionWith/intersectionWith/differenceWith instead.
innerMergeHash :: (Hashable a, Eq a)
               => Lens' s a -> Lens' t a
               -> (NonEmpty s -> NonEmpty t -> c)
               -> NonEmpty s -> NonEmpty t -> HashMap a c

outerMergeHash :: (Hashable a, Eq a)
               => Lens' s a -> Lens' t a
               -> (These (NonEmpty s) (NonEmpty t) -> c)
               -> NonEmpty s -> NonEmpty t -> HashMap a c
```

The `Hashed a` wrapper (caches hash) could also serve as an
optimization for repeated lookups — a Sort carrier that uses
`Hashed k` instead of `k` avoids rehashing.

### Hashable vs Ord design axis

| | Ord k | Hashable k |
|---|---|---|
| **Grouping** | Sorted (Map) | Unsorted (HashMap) |
| **mkSort1** | `Map.fromListWith` | `HashMap.fromListWith` |
| **Complexity** | O(n log n) | O(n) average |
| **Output** | `Map k v` | `HashMap k v` |
| **Sort3 carrier** | `mkSort3N` with Map | `mkSort3NH` with HashMap |
| **Merge** | `Map.merge` (WhenMatched/WhenMissing) | `unionWith`/`intersectionWith` (simpler) |

Both share the same Sort profunctor types — the difference is
only in the carrier construction (`mkSort1` vs `mkSort1H`) and
output container type.

Note: `unordered-containers` does NOT have a `WhenMatched`/
`WhenMissing` merge framework. Merge operations use inline
combining functions (`unionWith`, `intersectionWith`,
`differenceWith`). The `sortedMatched`/`sortedMissing` bridge
is containers-only. For HashMap merges, use the simpler
`innerMergeHash`/`outerMergeHash` operators.

## Hedgehog properties

| Prop  | Description                                                      |
|-------|------------------------------------------------------------------|
| P61   | `sortingVectorOf` groups share same key (via lens)               |
| P62   | `sortingVectorOf` preserves element count                        |
| P63   | `vectorGrate`: `over vectorGrate id v == v`                      |
| P64   | `sortingPrimArray` groups by key correctly                       |
| P65   | `sortingPrimArray` preserves element count                       |
| P66   | `mkSort3Ix` with 2D bounds groups correctly                      |
| P67   | `sortingArray` preserves all (index, element) pairs              |
| P68   | `arrayGrate`: `over arrayGrate id arr == arr`                    |
| P69   | `sortingRep` agrees with `sortingVector` for boxed Vector        |
| P70   | `sortingRep` agrees with `sortingPrimArray` for PrimArray        |
| P71   | `groupingHashOf` groups share same key                           |
| P72   | `groupingHashOf` preserves element count                         |
| P73   | `toHashMapOf` keys = set of focused values                       |
| P74   | `countingHashOf` counts agree with `countingOf` (same data)      |

## Work order

1. S6.5 — Generic `sortingRep` (establishes the pattern)
2. S6.1 — Boxed Vector optics + P61–P63
3. S6.6 — Test skeletons for P64–P70
4. S6.2 — Unboxed Vector optics
5. S6.3 — PrimArray optics + P64–P65
6. S6.4 — Array optics + P66–P68
7. S6.6 — Hashable-keyed grouping + P71–P74
8. Green P61–P74

## Key files

- `profunctor-optics-sort/src/Data/Profunctor/Optic/Sort.hs` — sortingRep, sortingVectorOf
- `profunctor-optics-sort/src/Data/Profunctor/Sort.hs` — mkSort3Ix
- New modules TBD: may create in profunctor-optics-sort or in
  a new profunctor-optics-arrays package
- `/Users/cmk/Documents/Code/haskell/vector/vector/src/Data/Vector.hs` — reference
- `/Users/cmk/Documents/Code/haskell/primitive/Data/Primitive/PrimArray.hs` — reference
- `/Users/cmk/Documents/Code/haskell/array/Data/Array/IArray.hs` — reference
- `/Users/cmk/Documents/Code/haskell/hashable/src/Data/Hashable.hs` — reference

## Dependencies

Will need to add to profunctor-optics-sort (or a new package):
- `vector` (already added)
- `primitive`
- `array`
- `hashable`
- `unordered-containers` (for HashMap output)

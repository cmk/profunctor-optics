# Sequences redesign evaluation

## Question

Should `profunctor-optics-sequences` drop `mono-traversable` in
favor of direct optics per container backend?

## Current state

`profunctor-optics-sequences` uses `MonoTraversable`, `IsSequence`,
`LazySequence` from `mono-traversable` to provide generic sequence
optics: `packing`, `chunking`, `taken`, `filteredBy`, `partitioned`,
`splitWhen`, etc. These work over any `IsSequence` instance.

## Arguments for dropping mono-traversable

1. **SortF needs `generate`/`index`/`length`, not `otraverse`.**
   The representable structure (Int-indexed) is what Sort uses.
   `mono-traversable` doesn't expose this — it exposes sequential
   traversal, which is the Strong/Traversing side, not the
   Closed/Cotraversing side.

2. **Concrete instances are simpler.** `sortingVectorF`,
   `sortingBytes`, `sortingChars` are each ~5 lines with no
   typeclass machinery. The functions are clear about what
   container they operate on.

3. **Different backends have different capabilities.** Vector has
   O(1) slicing, PrimArray has unboxed elements, Array has
   Ix-indexed multi-dimensional access. A single typeclass
   flattens these distinctions.

4. **Dependency weight.** `mono-traversable` pulls in
   `mono-traversable`, `vector`, `bytestring`, `text`,
   `unordered-containers`, and more. Per-backend packages
   can depend on only what they need.

5. **The profunctor-native approach is Closed/Costar, not
   Traversable.** Cotraversals, grates, and SortF are the
   Closed-side story. `mono-traversable` is the Strong-side
   story. The two don't overlap much.

## Arguments for keeping mono-traversable

1. **The Strong-side optics (traversals, folds) are useful.**
   `filteredBy`, `partitioned`, `takenWhile` etc. use
   `MonoTraversable` legitimately for sequential access.

2. **Users familiar with mono-traversable get a familiar API.**

3. **Some optics genuinely are container-generic.** `packing`
   (list → sequence) and `chunking` (strict → lazy) work
   across all IsSequence types.

## Recommendation

**Split the package. Keep mono-traversable for the Strong-side
traversal optics. Add per-backend Sort/Closed optics separately.**

The resulting structure:

| Package | Deps | Contents |
|---|---|---|
| `profunctor-optics-sequences` | mono-traversable | `filteredBy`, `partitioned`, `taken`, `packing`, `chunking`, Moore/Mealy operators |
| `profunctor-optics-sort` | vector, bytestring, text, containers | SortF, Sort1/Sort2, all sort/group/merge operators, `sortingVectorF`, `sortingBytes`, `sortingChars` |
| (future) per-backend modules | primitive, array | PrimArray/Array sort operators, grates, Ix-indexed SortF carriers |

The SortF operators don't need `mono-traversable` at all — they
work through `generate`/`index`/`length` which are concrete per
backend. The sequential traversal optics (Moore/Mealy/filtering)
legitimately use `MonoTraversable` and should stay where they are.

## Which sequence types benefit from SortF?

All Int-indexed representable types:

| Type | Index | SortF carrier | Notes |
|---|---|---|---|
| `Vector a` | Int | `mkSortFN` | Already done |
| `ByteString` | Int | `mkSortFN` | Already done (`sortingBytes`) |
| `Text` | Int | `mkSortFN` | Already done (`sortingChars`) |
| `PrimArray a` | Int | `mkSortFN` | Sprint 6 |
| `Array i e` | `Ix i` | `mkSortFIx` | Sprint 6 |
| `Seq a` | Int | `mkSortFN` | O(log n) index, same pattern |
| `UArray i e` | `Ix i` | `mkSortFIx` | Same as Array |

Types that do NOT benefit from SortF (not representable):
- Lazy ByteString/Text (chunked, not flat-indexed)
- Lists (no O(1) index)
- Sets/Maps (tree-indexed, use merge API instead)

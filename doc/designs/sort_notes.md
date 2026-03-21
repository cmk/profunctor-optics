# Sort Design Notes

## Sprint 4 summary

Sprint 4 is done. Here's the summary:

**11 commits on `feat/sort`**, 35 passing properties.

**Sort3 instance table (final):**
```
               Profunctor  Strong  Choice(†)  Closed  Costrong  Cosieve  Corepresentable
Sort3 i j k       ✓                  ✓          ✓       ✓         ✓           ✓

(†) Monoid i required for Choice, which unlocks Coaffine and Cotraversing
```

**Verified composition paths:**
- `grate8` via `sortingUnder` (Closed)
- `bits8` via `cosortingOf` (Cotraversal = Coaffine + Cotraversing)
- `ibits8` directly (Cxlens = coindexed Closed)
- `zipsSorting` for pointwise merging of Sort3 results

## Relens/Reprism as sort transformers

**Relens/Reprism are sort *transformers*, not sort *constructors*.** They post-process existing carriers rather than building new ones:

| Optic | Instance | Direction | What it does to a Sort carrier |
|---|---|---|---|
| `fstL` (Lens) | Strong | lift | int-sort → pair-sort (carry context) |
| `re fstL` (Relens) | Costrong | collapse | pair-sort → int-sort (knot-tie away context) |
| `left'` (Prism) | Choice | lift | a-sort → Either-sort (branch) |
| `releft` (Reprism) | Cochoice | collapse | Either-sort → a-sort (filter branch) |

Sort2 accepts all four directions. Sort3 accepts Relens (Costrong) unconditionally, and with `Monoid i` also accepts the Choice/Cochoice directions.

The `re` function is the bridge — it lets you use any Lens as a Relens and any Prism as a Reprism, which means you get both "lift" and "collapse" operations from a single optic definition.

## Indexed/coindexed optic composition

**Sort1 + indexed optics (Strong):**
- `sortingIx :: Ixlens' k s a -> NonEmpty (k, s) -> [NonEmpty s]` — the index IS the discrimination key. Works because `Ix p k a b = p (k, a) b` and Sort1 has Strong, so the `(k, a)` pair threads through naturally.

**Sort3 + coindexed optics (Closed):**
- `ibits8 :: Cxlens I8 Word8 Word8 Bool Bool` composes directly with Sort3 (P32 verifies this). The coindex `I8` (bit position) flows through Sort3's Closed instance. The carrier needs `rmap const mkSort3` to account for the `Cx p k a b = p a (k -> b)` wrapping.

**Sort3 + cotraversals (Cotraversing, Monoid i):**
- `bits8 :: Cotraversal Word8 Word8 Bool Bool` composes with Sort3 when `Monoid i` (P31). This required the new `Choice` instance on Sort3. The cotraversal's `Coaffine + Cotraversing` constraint is fully satisfied.

**What hasn't been explored yet:**
- **Sort1 + indexed traversals** (`Ixtraversal`) — Sort1 has Strong but not Traversing, so it can't carry a full indexed traversal. It can carry `Ixlens` and `Ixtraversal0` (Affine = Strong + Choice).
- **Sort2 + coindexed optics** — Sort2 has Strong + Choice + Costrong + Cochoice but NOT Closed, so it can't carry `Cxlens` or `Cxtraversal`. The coindexed path is Sort3-only.
- **Sort3 + Rxlens / Rxprism** (coindexed relens/reprism from Import.hs) — Sort3 has Costrong, and with `Monoid i` has Choice + Cochoice. So `Rxlens` (Costrong indexed) should work unconditionally, and `Rxprism` (Cochoice indexed) should work with `Monoid i`. These haven't been tested yet.
- **Composing indexed and coindexed** — e.g. `sortingIx someIxlens . cosortingOf bits8` chains, with the index accumulating monoidally via `%`. Not tested.

The short answer: yes, the indexed path works via Sort1 (Strong), the coindexed path works via Sort3 (Closed), and the two are complementary — exactly mirroring the Strong-vs-Closed split in the Sort type family. Sort2 lives in the middle but only on the indexed side (it has Strong but not Closed).

## Sort3 and representable containers (strings README connection)

This clicks several things into place for Sort3.

The `bits8`/`grate8` story is essentially: `Word8 ≅ (I8 -> Bool)` — a Word is a representable container of bits. And Sort3's input is `(i -> (k, a))` — a representable container of keyed values. These are the same shape.

**Sort3 as a radix sort step:**

If `i = I8`, `k = Bool` (bit value as key), `a = Bool`, then `Sort3 I8 j Bool Bool Bool` is: "given a tabulation of 8 keyed bits, produce a result indexed by group and key." That's a single radix sort pass — partition bits into `False`-bucket and `True`-bucket.

**Colens composition already works:**

`grate8 :: Colens Word8 Word8 (I8 -> Bool) (I8 -> Bool)` can lift a Sort3 through `sortingUnder grate8`, sorting at the bit-representation level. The `zipsWith` operation on grates means you could also combine/merge sort results pointwise across two Word8s.

**Cotraversal composition (Monoid i):**

`bits8 :: Cotraversal Word8 Word8 Bool Bool` could compose with Sort3 when `i` is a Monoid, since Sort3 then satisfies `Cotraversing`. This would let you sort/group at the individual-bit level through the cotraversal.

**Indexed cotraversal (Cxlens):**

`ibits8` gives position-aware access — the index IS the bit position. This maps directly onto Sort3's coindexed optic carrier shape:

```
Cxtraversal k s t a b ≅ (f a -> k -> b) -> f s -> t
Sort3 i j k a b       ≅ (i -> (k, a)) -> j -> k -> b
```

So `ibits8` can thread bit positions through Sort3 as coindices.

**Concrete `mkSort3` candidate:**

For `Fin n`-indexed types (like `I8` from scheme-extensions), a natural `mkSort3` would be:

```haskell
mkSort3 :: (Bounded i, Enum i, Ord k) => Sort3 i Int k a a
```

The exact semantics need experimentation, but the Word optics give a concrete playground where `i` is finite and enumerable.

## Containers merge integration

The three levels of containers-merge integration:

**Level 1 (done):** Sort → Map → merge. Our `mergingOf` does this. Sort1 groups inputs into `Map a (NonEmpty s)`, then `Map.merge` combines two Maps. The merge walks the BSTs, Sort did the grouping. Two separate phases.

**Level 2 (done):** Sort3 as a merge tactic. `WhenMatched Identity k x y z` is `k -> x -> y -> Maybe z` — a newtype around a function. `WhenMissing` has both `missingKey :: k -> x -> Maybe y` and `missingSubtree :: Map k x -> Map k y`. We can construct these FROM Sort3 via `sortedMatched` and `sortedMissing`.

The carrier uses `i = ()` since a merge tactic has exactly one "position" per key. The carrier calls `inp ()` to receive the actual merge-time values — no `undefined` needed.

**Level 3 (future):** Sort3 as the merge *engine*. The `mergeA` implementation walks two BSTs simultaneously using `splitLookup`. Sort3's `(i -> (k, a))` tabulated input is a *representable* version of a BST — if `i` encodes BST paths, then `inp :: BSTPath -> (k, a)` is a direct readout of the tree structure. And `j -> k -> b` on the output side is the result tree addressed by path and key.

For this to work, `i` would need to encode something like the BST's node addresses. But Map's internal structure isn't exposed through a stable `Enum`/`Bounded` index — it's a recursive type. This is where the pattern functors from `profunctor-optics-containers` come in: `MapF k v r = MapTip | MapBin !Size !k v r r` gives one layer of the BST. With recursion schemes, `Map k v ≅ Mu (MapF k v)`, and the path through the tree is a sequence of `Left`/`Right` turns.

The deepest plug-in would be: Sort3 with `i = [Bool]` (BST path) operating on `MapF`-based representations. But this breaks the `Bounded`/`Enum` requirement of `mkSort3` since paths are variable-length.

Level 2 is the practical sweet spot. Level 3 would essentially reimplement `mergeA`'s BST walking logic using pattern functors and Sort3, which may not gain much over just using `mergeA` with Sort3 tactics.

## Sort → Map → Merge pipeline

```
NonEmpty s ──sortingOf o──→ [NonEmpty s] ──toMapOf o──→ Map a (NonEmpty s)
                                                              │
NonEmpty t ──sortingOf o──→ [NonEmpty t] ──toMapOf o──→ Map a (NonEmpty t)
                                                              │
                                            mergingOf ────────┘
                                               │
                                          Map a c
```

The `mergingOf` operator is the bridge: it takes two lenses (for key extraction), three containers merge tactics (left-missing, right-missing, matched), and two NonEmpty inputs, producing a merged Map. The convenience wrappers (`innerMerge`, `outerMerge`, `leftMerge`, `rightMerge`) pre-wire common tactic patterns.

This is strictly more powerful than the old `joiningOf` family because:
1. It uses optics (Lens) for key extraction instead of plain functions
2. It exposes the full WhenMissing/WhenMatched tactic vocabulary
3. Results are keyed Maps, not flat lists

## Sort3 as merge tactics

`sortedMatched` and `sortedMissing` let you construct `WhenMatched`/`WhenMissing` tactics FROM Sort3 carriers, which then plug directly into `Map.merge`. The Sort3 receives the actual merge-time values via `const` input function (`inp = const (k, val)`), and its profunctor instances remain available for transforming the tactic before plugging in.

The interesting part is what this buys you: since the Sort3 carriers are profunctor values, you can **compose optics with the merge tactics themselves**. For example, `sortingUnder grate8 matchTactic` would give you a merge tactic that operates at the bit-representation level, or `cosortingOf bits8 matchTactic` would give a tactic that merges through a cotraversal. The tactics are no longer opaque functions — they're profunctor carriers that participate in the optics composition story.

## Int-indexed containers (Vector)

The representable containers landscape:

| Container | Index type | Representable? | Sort3 `i` | Notes |
|---|---|---|---|---|
| `Word8` | `I8` | Yes (Distributive) | `I8` | Already working (bits8/grate8) |
| `Vector a` | `Int` | Yes (by position) | `Int` | `Int -> a` for valid indices |
| Strict `ByteString` | `Int` | Yes (byte array) | `Int` | `Int -> Word8` |
| Strict `Text` | `Int` | Yes (char array) | `Int` | `Int -> Char` |
| Lazy `ByteString` | `(Int, Int)` | Yes (chunk, offset) | `(Int, Int)` | Chunk-of-bytes |
| `Seq a` | `Int` | Yes (finger tree, O(log n)) | `Int` | Similar to Vector |

All the array-like types are representable by `Int` (or a product of `Int`s for chunked). The difference from `I8` is that `Int`-indexed containers have *dynamic* size — we can't enumerate `[minBound..maxBound]`. `mkSort3N` solves this by taking an explicit size parameter.

`sortingVector` groups a Vector by key via Sort3, materializing the result as `Map k (Vector a)`. Uses `mkSort3N` internally and runs through the Sort3 carrier for each group position.

## Design space coverage

**Covered:**
| Area | Sort variant | Status |
|---|---|---|
| Lens-based sorting/grouping/nubbing | Sort1 | Done (sortingOf, etc.) |
| Descending sort | Sort1, Sort2 | Done |
| Container construction (Map, counting) | Sort1 | Done (toMapOf, etc.) |
| Costrong/Cochoice grouping | Sort2 | Done (groupingBack, etc.) |
| Relens/Reprism as sort transformers | Sort2, Sort3 | Done (P36-P40) |
| Colens/grate composition | Sort3 | Done (sortingUnder + grate8) |
| Cotraversal composition (bits8) | Sort3 (Monoid i) | Done (cosortingOf) |
| Coindexed optics (ibits8) | Sort3 | Done (P32) |
| Indexed optics (Ixlens) | Sort1 | Done (sortingIx) |
| Merge pipeline (Sort → Map → merge) | Sort1 | Done (mergingOf, inner/outer/left/rightMerge) |
| Sort3 as merge tactics | Sort3 | Done (sortedMatched/sortedMissing) |
| Int-indexed containers (Vector) | Sort3 | Done (mkSort3N, sortingVector) |
| Pointwise Sort3 merging | Sort3 | Done (zipsSorting) |

**Remaining to explore before benchmarks:**
- ByteString/Text via Sort3 (representable by Int, similar to Vector)
- Whether to redesign profunctor-optics-sequences (drop mono-traversable?)
- Composing indexed + coindexed through a sort pipeline

**Ready to benchmark:**
- Sort1 `sortingOf` vs `Data.List.sort` vs `discrimination` sort
- Sort3 `sortingVector` vs `V.modify (VA.sort)`
- `toMapOf` vs `Map.fromListWith`
- `mergingOf` vs `Map.merge` directly

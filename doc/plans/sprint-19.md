# Sprint 19 — Container optic modules

## Scope

Fill API gaps in the 7 container optic modules to achieve consistency
across containers and with the core library.

## Stories

| ID | Target | Description |
|---|---|---|
| S19.1 | IntMap.Optic | Uncomment range queries (lookedLT/LE/GE/GT, updateLooked) |
| S19.2 | IntMap.Optic | Uncomment ixaltered', fix validated stub |
| S19.3 | IntMap.Optic | Add sort-based fold/mconcat operators (parity with Map) |
| S19.4 | Sequence.Optic | Add `at`/`ixat` for element access by index |
| S19.5 | Sequence.Optic | Add `ixtraversed`, `ixfolded`, `ixmapped` (parity with List) |
| S19.6 | Sequence.Optic | Add `folded` (non-indexed Fold) |
| S19.7 | Tree.Optic | Add recursive traversal over all nodes |
| S19.8 | Tree.Optic | Add fold over all tree values |
| S19.9 | Tree.Optic | Add depth-indexed traversal |
| S19.10 | List.Optic | Export non-indexed `traversed`, `folded`, `mapped` wrappers |
| S19.11 | Map/IntMap.Optic | Unify sort operator naming with sprint 18 renames |
| S19.12 | Map.Optic | Add dual optics: `zipsMap` Colens, `cxzipsMap` Cxlens |
| S19.13 | IntMap.Optic | Add dual optics: `zipsIntMap` Colens (parity with Map) |
| S19.14 | Set.Optic | Add dual optics: `zipsSet` Colens (set = predicate grate) |
| S19.15 | IntSet.Optic | Add dual optics: `zipsIntSet` Colens |
| S19.16 | Sequence.Optic | Add dual optics: `grateSeq` Colens, `cxtraversedSeq` |
| S19.17 | Tree.Optic | Add dual optics: `cotraversedTree`, `zipsTree` |
| S19.18 | List.Optic | Re-export `zipListed` Cosetter, add `zipsListWith` |
| S19.19 | All | Property tests for container optics |
| S19.20 | View.hs | Review/Rxview API: constructors, operators, MonadState |
| S19.21 | Prism.hs, Carrier.hs | Ixprism/Rxprism: ixleft/ixright/ixjust optics, Rxprism constructors |
| S19.22 | Setter.hs | cxsetter/cxsetter1 constructors (Cxoptic threading) |
| S19.23 | View.hs | cloneRxview (Cxoptic' Tagged path) |
| S19.24 | Property.hs, Test/ | Ixprism/Rxprism property predicates and hedgehog tests |
| S19.25 | Bench.hs, bench/ | Benchmark validation for Sprint 17 changes |
| S19.16 | All | Property tests for container optics |

## S19.1–S19.3 — IntMap parity with Map

IntMap.Optic has several commented-out functions that exist in Map.Optic.
The IntMap API supports these operations — they were likely deferred
rather than impossible.

Commented out (lines 21–25, 40):
- `updateLooked`, `lookedLT`, `lookedLE`, `lookedGE`, `lookedGT`
- `ixaltered'`

Note: IntMap doesn't have `lookupLT` etc. in `Data.IntMap`, so range
queries may need a different implementation (convert to Map, or binary
search on keys). Investigate feasibility before uncommenting.

`validated` on line 117 is `filtered (const True)` — a stub. Either
implement proper validation or remove.

Missing sort operators vs Map: `foldSorting`, `foldSorting1`,
`mconcatSorting`.

## S19.4–S19.6 — Sequence indexed optics

Seq supports efficient index-based access (`Seq.index`, `Seq.adjust`,
`Seq.update`) making indexed optics natural:

```haskell
at :: Int -> Traversal0' (Seq a) a
ixat :: Int -> Ixtraversal0' Int (Seq a) a
ixtraversed :: Ixtraversal Int (Seq a) (Seq b) a b
ixfolded :: Ixfold Int (Seq a) a
ixmapped :: Ixsetter Int (Seq a) (Seq b) a b
folded :: Fold (Seq a) a
```

## S19.7–S19.9 — Tree recursive optics

```haskell
-- Recursive traversal of all nodes (pre-order)
flattened :: Traversal' (Tree a) a

-- Fold over all values in the tree
folded :: Fold (Tree a) a

-- Depth-indexed traversal (index = depth from root)
ixflattened :: Ixtraversal Int (Tree a) (Tree b) a b
```

Implementation: `flattened` can use `traversalVl` with the existing
`Data.Tree.unfoldTree`/`foldTree` or manual recursion through
`rootLabel`/`subForest`.

## S19.10 — List non-indexed wrappers

List.Optic only exports indexed variants. Add thin wrappers or
re-exports for users who don't need indices:

```haskell
traversed :: Traversal [a] [b] a b  -- re-export from Traversal
folded :: Fold [a] a                -- re-export from Fold
mapped :: Setter [a] [b] a b       -- re-export from Setter
```

## S19.11 — Unify sort operator naming

Map.Optic uses `'` suffix (`toMapOf'`, `foldSorting'`), Sort.hs uses
`L` suffix, sprint 18 renames to active verbs. Apply the same rename
scheme here:

| Map.Optic current | Sprint 18 name |
|---|---|
| `toMapOf'` | `toMapOf` |
| `countingOf'` | `countsOf` |
| `foldSorting'` | `foldSorts` |
| `foldSorting1'` | `foldSorts1` |
| `mconcatSorting'` | `mconcatSorts` |
| `mergingOf'` | `merges` |
| `innerMerge'` | `innerMerges` |
| `outerMerge'` | `outerMerges` |
| `leftMerge'` | `leftMerges` |
| `rightMerge'` | `rightMerges` |

## S19.12 — Property tests

Add hedgehog property tests for:
- Map/IntMap: alteredF round-trip, ixtraversed identity, at/ixat laws
- Sequence: sliced identity, at round-trip
- Tree: root lens laws
- List: ixtraversed identity, at round-trip

## S19.12–S19.15 — Dual optics for containers

Any container isomorphic to a function from a finite index type
(`container ≅ index → element`) admits dual optics via
`Distributive`/`Representable`. See `Data.Word.Optic` in
profunctor-optics-strings for the pattern (bits8, ibits8, grate8).

### S19.12–S19.15 — Map/IntMap/Set/IntSet dual optics

All finite key-value containers are `Representable` when you fix the
key set. A set IS a function to `Bool`:

```haskell
-- Map: grate viewing Map as k → a
zipsMap :: Ord k => Set k -> Colens (Map k a) (Map k b) (k -> a) (k -> b)
cxzipsMap :: Ord k => Set k -> Cxlens k (Map k a) (Map k b) a b

-- IntMap: same pattern, Int-keyed
zipsIntMap :: IntSet -> Colens (IntMap a) (IntMap b) (Int -> a) (Int -> b)
cxzipsIntMap :: IntSet -> Cxlens Int (IntMap a) (IntMap b) a b

-- Set: grate viewing Set as a → Bool (predicate)
zipsSet :: Ord a => Set a -> Colens (Set a) (Set a) (a -> Bool) (a -> Bool)

-- IntSet: grate viewing IntSet as Int → Bool
zipsIntSet :: IntSet -> Colens IntSet IntSet (Int -> Bool) (Int -> Bool)
```

The Set/IntSet case is particularly nice — `zipsWith zipsSet (||) s1 s2`
is set union, `zipsWith zipsSet (&&) s1 s2` is intersection, all
expressed through the grate.

### S19.12 — Map dual optics (detail)

```haskell
-- Grate viewing Map as a function from keys (requires fixed key set)
zipsMap :: Ord k => Set k -> Colens (Map k a) (Map k b) (k -> a) (k -> b)
zipsMap ks = grate $ \f -> Map.fromSet (\k -> f (\m -> Map.findWithDefault err k m)) ks

-- Coindexed zipsWith for Map
cxzipsMap :: Ord k => Set k -> Cxlens k (Map k a) (Map k b) a b
```

Note: requires a key set to be `Representable`. The `rxmapped'` already
provides a coindexed review; these add the full grate/colens structure.

### S19.13 — Sequence dual optics

```haskell
-- Grate via Seq.index / Seq.fromFunction (requires known length)
grateSeq :: Int -> Colens (Seq a) (Seq b) (Int -> a) (Int -> b)
grateSeq n = grate $ \f -> Seq.fromFunction n (\i -> f (\s -> Seq.index s i))

-- Coindexed traversal via index
cxtraversedSeq :: Int -> Cxtraversal Int (Seq a) (Seq b) a b
```

### S19.14 — Tree dual optics

```haskell
-- Tree is a cofree comonad, so it's Cotraversable1
cotraversedTree :: Cotraversal1 (Tree a) (Tree b) a b

-- Pointwise zipping of trees (root with root, children with children)
zipsTree :: Colens (Tree a) (Tree b) a b
zipsTree = grate $ \f -> Node (f rootLabel) (zipWith (\l r -> ...) ...)
```

Note: `zipsTree` zips structurally — mismatched shapes truncate to the
shorter tree, like `ZipList`.

### S19.15 — List dual re-export

Re-export `zipListed` from Setter.hs into List.Optic for
discoverability. Also consider:

```haskell
-- Grate via ZipList (requires known length for safe indexing)
zipsListWith :: Colens [a] [b] a b
zipsListWith = dimap ZipList getZipList . distributed
```

## Work order

Phase 1 — IntMap parity:
  1. S19.1 (range queries)
  2. S19.2 (ixaltered', validated)
  3. S19.3 (sort fold operators)

Phase 2 — Sequence/Tree:
  4. S19.4 (Seq at/ixat)
  5. S19.5 (Seq indexed optics)
  6. S19.6 (Seq folded)
  7. S19.7–S19.9 (Tree recursive optics)

Phase 3 — Dual optics:
  8. S19.12 (Map dual optics)
  9. S19.13 (IntMap dual optics)
  10. S19.14 (Set dual optics)
  11. S19.15 (IntSet dual optics)
  12. S19.16 (Sequence dual optics)
  13. S19.17 (Tree dual optics)
  14. S19.18 (List dual re-export)

Phase 4 — Consistency:
  15. S19.10 (List non-indexed wrappers)
  16. S19.11 (naming unification with sprint 18)

Phase 5 — Carry-forward from Sprint 17:
  17. S19.20 (Review/Rxview API in View.hs)
  18. S19.21 (Ixprism/Rxprism: remaining optics, Rxprism constructors, property tests)
  19. S19.22 (cxsetter/cxsetter1 constructors)
  20. S19.23 (cloneRxview)
  21. S19.24 (Ixprism/Rxprism property predicates and hedgehog tests)
  22. S19.25 (Benchmark validation for Sprint 17 changes)

Phase 6 — Tests:
  23. S19.19 (property tests for container optics)

## S19.20 — Review/Rxview API

`Review = Costrong + CoercingL` is the true Re-dual of `View`. Needs:

```haskell
-- Constructors (View.hs)
reinto :: (b -> t) -> Review t b       -- dual of 'to', via re
cloneReview :: AReview t b -> Review t b

-- Operators (View.hs)
review :: AReview t b -> b -> t        -- distinct from coview
reviews :: AReview t b -> (t -> r) -> b -> r

-- Rxview (indexed Review)
type Rxview k t b = forall p. (Costrong p, CoercingL p) => Ixoptic' p k t b
rxinto :: ((k -> b) -> t) -> Rxview k t b
```

Note: `AReview = Optic' Tagged t b` is the same carrier as `ACoview`
since `Tagged` is both `Closed` and `Costrong`. The distinction is
in the polymorphic constraint, not the carrier.

## S19.21 — Ixprism/Rxprism remaining

Carry-forward from S17.25. Types and basic constructors done. Remaining:

```haskell
-- Optics (Prism.hs)
ixleft  :: Ixprism k (a + c) (b + c) a b
ixright :: Ixprism k (c + a) (c + b) a b
ixjust  :: Ixprism k (Maybe a) (Maybe b) a b

-- Rxprism constructors (Prism.hs)
rxprism  :: (s -> (k, a)) -> (b -> (k, a) + t) -> Rxprism k s t a b
rxprism' :: (s -> (k, a)) -> ((k, a) -> Maybe s) -> Rxprism' k s a
cloneRxprism :: ARxprism k s t a b -> Rxprism k s t a b

-- Operators
ixaside :: AIxprism k s t a b -> Ixprism k (e, s) (e, t) (e, a) (e, b)
```

## S19.22 — cxsetter/cxsetter1

Deferred from S17.27. The Cxoptic threading pattern (`p a (k -> b)`)
makes the standard `cosetter`-style construction non-trivial. Needs
investigation into how `coindexing` composes with `corepresenting`
for the coindexed case.

## S19.23 — cloneRxview

Deferred from S17.26. Cloning through the `Cxoptic' Tagged` path
requires understanding how `Tagged` interacts with the coindex
function space `k -> b`.

## S19.24 — Ixprism/Rxprism property tests

```haskell
-- Property.hs
tofrom_ixprism    :: (Eq s, Monoid k) => Ixprism' k s a -> s -> Bool
fromto_ixprism    :: (Eq s, Eq a, Eq k, Monoid k) => Ixprism' k s a -> a -> Bool
idempotent_ixprism :: (Eq s, Eq a, Eq k, Monoid k) => Ixprism' k s a -> s -> Bool

-- Test/Carrier.hs
prop_ixprism_tofrom :: Property
prop_ixprism_fromto :: Property
prop_ixprism_idempotent :: Property
```

## S19.25 — Benchmark validation

Verify Sprint 17 changes don't regress performance:

- cotraversal0 constructor (new): benchmark vs direct CPS
- Cofold constraint fix (Coaffine): verify cofoldMapOf still zero-cost
- coview/coviews rename: verify no regression vs old review
- Ixprism constructors: benchmark withIxprism extraction
- New clone functions: verify cloneTraversal0, cloneCotraversal0
- New fold constructors: benchmark ixfoldVl, cxfoldVl paths

Run the existing benchmark suite and compare against the baseline
from Sprint 16.

## Key files

- `profunctor-optics/src/Data/IntMap/Optic.hs`
- `profunctor-optics/src/Data/Sequence/Optic.hs`
- `profunctor-optics/src/Data/Tree/Optic.hs`
- `profunctor-optics/src/Data/List/Optic.hs`
- `profunctor-optics/src/Data/Map/Optic.hs`
- `profunctor-optics/test/Test/Data/*/Optic.hs`

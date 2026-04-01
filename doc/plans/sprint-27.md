# Sprint 27 — vector-optics: profunctor optics for Data.Vector

## Goal

New library `vector-optics` providing profunctor optics for `Data.Vector`,
`Data.Vector.Unboxed`, and `Data.Vector.Storable`. Follows the same patterns
as the Seq, IntMap, Map, Text, and ByteString optic modules.

## Design decisions

### Generic vs concrete

Vector provides `Data.Vector.Generic` with a typeclass-based API. Options:

1. **Concrete modules** — `Data.Vector.Optic`, `Data.Vector.Unboxed.Optic`,
   `Data.Vector.Storable.Optic` with duplicated code
2. **Generic module** — `Data.Vector.Generic.Optic` using the `Vector` typeclass,
   with thin concrete re-exports

Option 2 is cleaner. Most optics can be defined once against the generic
interface. Concrete modules re-export with monomorphized types.

### Index type

`Sum Int` — consistent with Seq, List, IntMap, Text, ByteString.

### Naming

Follow established container patterns:
- Non-indexed optics with key parameter: `at`, etc.
- Indexed versions that drop the parameter: `ixat`, `ixtraversed`, etc.
- Coindexed duals: `cxtraversed`, `cxfolded`, `cxmapped`, `cxfiltered`

## Optic mapping

### Isos

| Name | Type | Upstream |
|------|------|----------|
| `reversed` | `Iso' (Vector a) (Vector a)` | `reverse`/`reverse` |
| `packed` | `Iso' [a] (Vector a)` | `fromList`/`toList` |

### Prisms

| Name | Type | Upstream |
|------|------|----------|
| `consed` | `Prism' (Vector a) (a, Vector a)` | `uncons`/`cons` |
| `snoced` | `Prism' (Vector a) (Vector a, a)` | `unsnoc`/`snoc` |

### Traversal0 / Fold0

| Name | Type | Upstream |
|------|------|----------|
| `at` | `Int -> Traversal0' (Vector a) a` | `(!?)` / update via `(//)` |
| `ixat` | `Ixtraversal0' (Sum Int) (Vector a) a` | incoming index = position |
| `found` | `(a -> Bool) -> Traversal0' (Vector a) a` | `find` / replace first match |
| `headed` | `Fold0 (Vector a) a` | safe `head` |
| `lasted` | `Fold0 (Vector a) a` | safe `last` |
| `foundIndex` | `(a -> Bool) -> Fold0 (Vector a) (Sum Int)` | `findIndex` |
| `foundIndexR` | `(a -> Bool) -> Fold0 (Vector a) (Sum Int)` | `findIndexR` |
| `elemIndexed` | `Eq a => a -> Fold0 (Vector a) (Sum Int)` | `elemIndex` |

### Traversals

| Name | Type | Upstream |
|------|------|----------|
| `traversed` | re-export from Traversable | `traverse` |
| `ixtraversed` | `Ixtraversal (Sum Int) (Vector a) (Vector b) a b` | `itraverse` / `imap` |
| `slicedTo` | `Int -> Traversal' (Vector a) a` | traverse first n |
| `slicedFrom` | `Int -> Traversal' (Vector a) a` | traverse after n |
| `sliced` | `Int -> Int -> Traversal' (Vector a) a` | traverse range [i,j) |

### Folds

| Name | Type | Upstream |
|------|------|----------|
| `folded` | re-export from Foldable | `foldMap` |
| `ixfolded` | `Ixfold (Sum Int) (Vector a) a` | `ifoldMap` / `ifoldr` |

### Notes on monadic variants

`mapM`, `imapM`, `forM` are subsumed by the traversals:

```haskell
traverseOf ixtraversed f v ≡ V.imapM (curry f) v  -- (modulo Sum wrapping)
traverseOf traversed f v   ≡ V.mapM f v
```

`generateM :: Monad m => Int -> (Int -> m a) -> m (Vector a)` is the monadic
version of `generate`. It doesn't add a new optic — it's `generate` lifted
into a monad. The `cxzipped` Cxlens covers the pure case; monadic generation
is done via `traverseOf (cxzipped n)`.

Similarly `replicateM`, `iterateNM`, `unfoldrM`, `unfoldrNM`, etc. are monadic
lifts of their pure counterparts and don't need separate optics.

### Setters / Ixsetters

| Name | Type | Upstream |
|------|------|----------|
| `mapped` | `Setter (Vector a) (Vector b) a b` | `map` |
| `ixmapped` | `Ixsetter (Sum Int) (Vector a) (Vector b) a b` | `imap` |
| `adjusted` | `Ixsetter' (Sum Int) (Vector a) a` | incoming index, modify at position |
| `sorted` | `Ord b => Adjoint (Vector a) (Vector a) a b` | via list sort — no native `sortOn` |
| `filtered` | `Adjoint (Vector a) (Vector a) a Bool` | `filter` |
| `ixfiltered` | `Ixsetter (Sum Int) (Vector a) (Vector a) a Bool` | `ifilter` |

### Indexed Adjoint

| Name | Type | Upstream |
|------|------|----------|
| `mappedMaybe` | `Ixadjoint (Sum Int) (Vector a) (Vector b) a (Maybe b)` | `imapMaybe` — indexed map+filter. No `ix` prefix (only version). |

### Cxlens (dual side)

| Name | Type | Upstream |
|------|------|----------|
| `zipped` | `Int -> Cxlens (Sum Int) (Vector a) (Vector b) a b` | `generate n` — coindexed representable functor tabulation |

`generate :: Int -> (Int -> a) -> Vector a` is the tabulation. The `Cxlens`
threads the position as coindex `Sum Int`, giving focus `a`. No `Colens`
with `Int -> a` focus (avoid `(->)` in optic holes).

`constructN`/`constructrN` are subsumed — the prefix-dependent building is
an implementation detail.

### Cotraversals

| Name | Type | Upstream |
|------|------|----------|
| `zippedTraverse` | `Int -> Cotraversal (Vector a) (Vector b) a b` | pointwise at known length |
| `zippedWith` | `Cotraversal (Vector a) (Vector b) a b` | `zipWith` (truncates to shorter) |

### Coindexed optics

| Name | Type | Upstream |
|------|------|----------|
| `cxtraversed` | `Cxtraversal (Sum Int) (Vector a) (Vector b) a b` | dual of `ixtraversed` |
| `cxfolded` | `Cxfold (Sum Int) (Vector a) a` | dual of `ixfolded` |
| `cxmapped` | `Cxsetter (Sum Int) (Vector a) (Vector b) a b` | dual of `ixmapped` |
| `cxfiltered` | `Cxsetter (Sum Int) (Vector a) (Vector a) a Bool` | coindexed filter |

### Cofolds

| Name | Type | Upstream |
|------|------|----------|
| `unfolded` | `Cofold (Vector a) a` | `unfoldr` as anamorphism |
| `unfoldedN` | `Int -> Cofold (Vector a) a` | `unfoldrN` (bounded) |

### Adjoints (both sides)

| Name | Type | Upstream |
|------|------|----------|
| `partitioned` | `Adjoint (Vector a) (Vector a, Vector a) a Bool` | `partition` |
| `mapped` | already listed | |
| `filtered` | already listed | |

### Bulk updates (Vector-specific)

| Name | Type | Upstream |
|------|------|----------|
| `accumulated` | `Ixadjoint (Sum Int) (Vector a) (Vector a) a a` | `accum` / `accumulate` — indexed update |
| `backpermuted` | `Adjoint (Vector a) (Vector a) (Vector Int) (Vector Int)` | `backpermute` — reindex by permutation vector |

## Module structure

```
vector-optics/
  src/
    Data/Vector/Generic/Optic.hs     -- generic implementations
    Data/Vector/Optic.hs             -- boxed re-exports
    Data/Vector/Unboxed/Optic.hs     -- unboxed re-exports
    Data/Vector/Storable/Optic.hs    -- storable re-exports
  test/
    Test/Data/Vector/Optic.hs
  vector-optics.cabal
```

## Implementation approach

### Generic module

Most optics defined once using `Data.Vector.Generic`:

```haskell
import qualified Data.Vector.Generic as G

reversed :: G.Vector v a => Iso' (v a) (v a)
reversed = iso G.reverse G.reverse

consed :: G.Vector v a => Prism' (v a) (a, v a)
consed = prism' G.uncons (\(a, v) -> G.cons a v)

ixtraversed :: G.Vector v a => G.Vector v b
            => Ixtraversal (Sum Int) (v a) (v b) a b
ixtraversed = ixtraversalVl $ \f k v ->
  G.fromListN (G.length v) <$>
    traverse (\(i, a) -> f (k <> Sum i) a) (zip [0..] (G.toList v))
```

### Concrete re-exports

```haskell
-- Data/Vector/Optic.hs
module Data.Vector.Optic (
    reversed, consed, snoced, ...
) where

import Data.Vector.Generic.Optic
```

Monomorphized type signatures via type annotations or wrapper newtypes
where needed (especially for Unboxed/Storable which have class constraints).

### Performance notes

- `G.toList`/`G.fromList` round-trips are O(n) but unavoidable for
  profunctor traversals that need element-by-element access
- `G.generate n f` is O(n) and avoids intermediate lists for known-length
  operations
- `imap`, `ifilter`, `ifoldr` are native O(n) and should be used
  directly in setter/fold implementations rather than going through lists
- The `modify` function gives O(1) in-place updates for mutable use cases,
  but profunctor optics are pure — `(//)` is the pure equivalent

## Property testing approach

### Iso laws

```haskell
prop_reversed_involutive v = V.reverse (V.reverse v) == v
prop_packed_roundtrip xs = V.toList (V.fromList xs) == xs
```

### Prism laws

```haskell
prop_consed_tofrom (a, v) = preview consed (review consed (a, v)) == Just (a, v)
prop_consed_fromto v = maybe v (review consed) (preview consed v) == v
```

### Indexed threading

```haskell
-- ixtraversed indices are correct positions
prop_ixtraversed_indices v =
  fmap fst (ixtoListOf ixtraversed v) == [Sum i | i <- [0 .. V.length v - 1]]

-- (.) accumulates indices
prop_ix_dot_accumulates =
  let vv = V.fromList [V.fromList [10,20], V.fromList [30]]
      result = B.first getSum <$> ixtoListOf (ixtraversed . ixtraversed) vv
  in result == [(0,10),(1,20),(1,30)]

-- ixmapped agrees with V.imap
prop_ixmapped_eq v =
  ixsets ixmapped (\k a -> a + getSum k) v == V.imap (\i a -> a + i) v

-- ixfiltered agrees with V.ifilter
prop_ixfiltered_eq v =
  ixsets ixfiltered (\k _ -> even (getSum k)) v == V.ifilter (\i _ -> even i) v
```

### Coindexed equivalence

```haskell
-- cxmapped agrees with V.imap
prop_cxmapped_eq v =
  cxsets cxmapped (\k a -> a + getSum k) v == V.imap (\i a -> a + i) v

-- cxzipped identity
prop_cxzipped_id v =
  let n = V.length v
  in cxsets (cxzipped n) (\_ a -> a) v == v

-- cxzipped indices
prop_cxzipped_indices =
  let v = V.fromList [10,20,30 :: Int]
  in cxsets (cxzipped 3) (\k a -> a + getSum k) v == V.fromList [10,21,32]
```

### Fold0 equivalence

```haskell
prop_headed_eq v = preview headed v == (if V.null v then Nothing else Just (V.head v))
prop_lasted_eq v = preview lasted v == (if V.null v then Nothing else Just (V.last v))
prop_foundIndex_eq v =
  let p = (> 50)
  in fmap getSum (preview (foundIndex p) v) == V.findIndex p v
```

### Adjoint laws

```haskell
prop_filtered_id v = sets filtered (const True) v == v
prop_filtered_eq p v = sets filtered p v == V.filter p v
```

## Ordering

1. **Phase 1**: Generic module with Isos, Prisms, Traversal0/Fold0
2. **Phase 2**: Indexed optics (ixtraversed, ixfolded, ixmapped, ixfiltered, ixat, adjusted)
3. **Phase 3**: Coindexed optics (cxtraversed, cxfolded, cxmapped, cxfiltered, cxzipped)
4. **Phase 4**: Setters, Adjoints (filtered, sorted, imapMaybed)
5. **Phase 5**: Dual optics (zipped, zippedTraverse, Cofolds)
6. **Phase 6**: Concrete re-export modules (Vector, Unboxed, Storable)
7. **Phase 7**: Property tests

Each phase is a separate commit.

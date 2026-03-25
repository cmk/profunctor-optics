# Dual optic use cases — containers, unordered-containers, vector, text, bytestring

## Current state

The library already has dual (Costar-side) optics for containers:

| Module | Dual Optic | Type |
|--------|-----------|------|
| Map.Optic | `zipsMap` | `Set k -> Colens (Map k a) (Map k b) (k -> a) (k -> b)` |
| Map.Optic | `cxmapped'` | `Cxview k (Map k a -> Map k b) (a -> b)` |
| IntMap.Optic | `zipsIntMap` | `IntSet -> Colens (IntMap a) (IntMap b) (Int -> a) (Int -> b)` |
| IntMap.Optic | `cxmapped` | `Cxview Int (IntMap a -> IntMap b) (a -> b)` |
| Set.Optic | `zipsSet` | `Set a -> Colens (Set a) (Set a) (a -> Bool) (a -> Bool)` |
| Sequence.Optic | `grateSeq` | `Int -> Colens (Seq a) (Seq b) (Int -> a) (Int -> b)` |
| List.Optic | `zipsListWith` | `Int -> Colens [a] [b] a b` |
| Setter | `coliftedA` | `Applicative f => Cosetter (f a) (f b) a b` |
| Setter | `zipListed` | `Cosetter [a] [b] a b` |

These are all **Colens** (viewing containers as functions from their index type)
or **Cosetter/Cxview** (pointwise operations). The dual optic surface is thin
compared to the primary (Star-side) optics.

## Opportunities by dual optic type

### Cxsetter — keyed transformations (highest value)

The `*WithKey` family from containers maps directly to `Cxsetter`:

```haskell
-- Map.mapWithKey :: (k -> a -> b) -> Map k a -> Map k b
-- This IS cxsets applied to the right optic:
--   cxsets ixmapped :: (k -> a -> b) -> Map k a -> Map k b

-- Map.mapMaybeWithKey :: (k -> a -> Maybe b) -> Map k a -> Map k b
cxmapMaybe :: Ord k => Cxsetter k (Map k a) (Map k b) a (Maybe b)

-- Map.filterWithKey :: (k -> a -> Bool) -> Map k a -> Map k a
cxfiltered :: Ord k => Cxsetter k (Map k a) (Map k a) a Bool

-- HashMap.mapWithKey, filterWithKey, mapMaybeWithKey — same shapes
```

The library already has `ixmapped` (Star-side indexed setter for maps).
The Cx duals would give the same operations but threading the key on
the Costar side, composable with Colens/Cotraversal chains.

**Concrete additions for Map.Optic:**

```haskell
-- Coindexed filter: keep entries where the predicate holds
cxfiltered :: Ord k => Cxsetter k (Map k a) (Map k a) a Bool
cxfiltered = cxsetter $ \kab -> Map.filterWithKey (\k a -> kab k a)

-- Coindexed mapMaybe: transform and filter simultaneously
cxmapMaybed :: Ord k => Cxsetter k (Map k a) (Map k b) a (Maybe b)
cxmapMaybed = cxsetter $ \kab -> Map.mapMaybeWithKey kab
```

**For unordered-containers:**

```haskell
-- Same shapes, just Hashable instead of Ord
cxfiltered :: (Eq k, Hashable k) => Cxsetter k (HashMap k a) (HashMap k a) a Bool
cxmapMaybed :: (Eq k, Hashable k) => Cxsetter k (HashMap k a) (HashMap k b) a (Maybe b)
```

### Cxfold — keyed folds

```haskell
-- Map.foldMapWithKey :: Monoid m => (k -> a -> m) -> Map k a -> m
-- Map.foldrWithKey :: (k -> a -> b -> b) -> b -> Map k a -> b

-- Already possible via: cxfoldMapOf cxfolded
-- where cxfolded :: Cxfold k (Map k a) a
-- But a dedicated optic would be clearer.

-- HashMap.foldlWithKey', foldrWithKey, foldMapWithKey — same shapes
```

The library already has `ixfolded :: Ixfold k (Map k a) a`. A `cxfolded`
dual would compose with Costar-side optics. This might already work
via `cxmapped'` and existing machinery — worth checking.

### Cofold — recursive folds (Tree)

```haskell
-- Data.Tree.foldTree :: (a -> [b] -> b) -> Tree a -> b
--
-- This is a catamorphism: it consumes a recursive extractor.
-- Shape: ((a, [b]) -> b) -> Tree a -> b
-- This is Costar ((,) a . []) applied in a recursive context.
--
-- Not directly a Cofold (which is a Costar-side fold over a
-- Distributive functor), but the recursive structure suggests
-- a dedicated optic.

foldedTree :: Cofold (Tree b) b
-- or: cofoldTree :: (a -> [b] -> b) -> Tree a -> b
-- wrapped as a cosetter or cofold
```

Tree catamorphisms don't fit the standard Cofold pattern cleanly
because `Tree` is recursive, not Distributive. But `foldTree` could
be wrapped as a `Cosetter`:

```haskell
-- cosetter from the foldTree SEC:
foldedTree :: Cosetter (Tree a) b a ([b] -> b)
-- or more practically, a specialized operation
```

This needs more thought — the recursive structure may require a
dedicated combinator rather than a standard dual optic.

### Cotraversal — pointwise zipping

```haskell
-- Seq.zipWith :: (a -> b -> c) -> Seq a -> Seq b -> Seq c
-- Map.intersectionWith :: Ord k => (a -> b -> c) -> Map k a -> Map k b -> Map k c
-- HashMap.intersectionWith :: ... same shape
```

These are binary zip operations. They're naturally Costar-based:
given two containers and a combining function, produce a container.
The Cotraversal pattern `(f a -> b) -> f s -> t` captures this when
`f` is the "paired container" functor.

**For Map:**
```haskell
-- View two maps as a paired structure and zip pointwise
-- This extends zipsMap to handle two maps simultaneously
zippedMap :: Ord k => Set k -> Cotraversal (Map k a) (Map k b) a b
```

**For Seq:**
```haskell
-- Already covered by coliftedA at ZipList, but for Seq:
zippedSeq :: Int -> Cotraversal (Seq a) (Seq b) a b
```

### Cosort — keyed stream construction

`Cosort i k a b = a -> k -> (i, b)` — given a value and a key, produce
an indexed result. This is the Star-side dual of Sort's Costar-side
stream consumption.

**Use case: keyed insertion/construction**

```haskell
-- Map.fromSet :: (k -> a) -> Set k -> Map k a
-- This constructs a Map by applying a function to each key.
-- As a Cosort: for each key, produce a value.

-- Map.mapWithKey :: (k -> a -> b) -> Map k a -> Map k b
-- As a Cosort: for each (value, key), produce a new value.

-- The Sort-based merge operations already handle the Costar side.
-- Cosort would handle the Star side: constructing keyed results.
```

Cosort's main value is as the Star-side carrier for Sort-based
pipelines. When you need to BUILD keyed containers (rather than
CONSUME them), Cosort provides the representation.

**Concrete example:**

```haskell
-- Given a Sort pipeline that groups data, Cosort could wrap the
-- reconstruction step:
--
-- Sort:   (i -> (k, a)) -> Map k [a]     -- group by key
-- Cosort: a -> k -> (i, Map k [a])       -- annotate with key + index
--
-- The sortCosort bridge connects them.
```

### ContJoin — continuation-based operations (speculative)

`ContJoin j a b = ((a -> j) -> j) -> b` — Corep = Cont j.

**Potential use case: CPS folds**

```haskell
-- foldMap :: Monoid m => (a -> m) -> f a -> m
-- is "given a way to turn elements into a monoid, fold the container"
--
-- In CPS: ((a -> m) -> m) is Cont m a
-- So: foldMap f = runCont (traverse (Cont . flip ($)) container) f
--
-- ContJoin would be the profunctor for operations that consume
-- continuations over elements.
```

This is more theoretical than practical. The Cont-based view of
folds is elegant but doesn't obviously give new operations beyond
what Cofold already provides. ContJoin's main value is structural
(it's the profunctor at the contravariant self-adjunction) rather
than operational.

### Merge operations — Sort + containers merge API

The containers `Map.merge` API with `WhenMissing`/`WhenMatched`
tactics is partially captured by `sortedMatched`/`sortedMissing`.
The unordered-containers equivalents (`unionWithKey`,
`intersectionWithKey`, `differenceWithKey`) are not.

**For HashMap:**

```haskell
-- HashMap.unionWithKey :: (k -> v -> v -> v) -> HashMap k v -> HashMap k v -> HashMap k v
-- HashMap.intersectionWithKey :: (k -> v1 -> v2 -> v3) -> HashMap k v1 -> HashMap k v2 -> HashMap k v3
-- HashMap.differenceWithKey :: (k -> v -> w -> Maybe v) -> HashMap k v -> HashMap k w -> HashMap k v

-- These could be wrapped as Sort-based merge combinators:
innerMergesHash :: (Eq k, Hashable k)
    => (k -> a -> b -> c) -> HashMap k a -> HashMap k b -> HashMap k c
innerMergesHash = HashMap.intersectionWithKey

outerMergesHash :: (Eq k, Hashable k)
    => (k -> a -> c) -> (k -> b -> c) -> (k -> a -> b -> c)
    -> HashMap k a -> HashMap k b -> HashMap k c
-- Needs unionWith + intersectionWith combination
```

The Sort module's lens-based merge operators (`merges`, `innerMerges`,
etc.) already provide this for `Map`. Extending to `HashMap` would
require either:
1. Abstracting the merge interface over a type class
2. Duplicating the combinators for HashMap

### fromSet / fromList as Colens

```haskell
-- Map.fromSet :: (k -> a) -> Set k -> Map k a
-- Constructs a Map by evaluating a function at each key.
-- This is a Colens: the Map IS the function, viewed through the key set.

fromSetColens :: Ord k => Set k -> Colens (Map k a) (Map k b) (k -> a) (k -> b)
-- This is exactly zipsMap! Already in the library.

-- Map.fromSetA :: Applicative f => (k -> f a) -> Set k -> f (Map k a)
-- Effectful variant — could be a Cotraversal
fromSetCotraversal :: (Ord k, Applicative f)
    => Set k -> Cotraversal (Map k a) (Map k b) (k -> a) (k -> b)
-- But this is the same as zipsMap composed with effectful operations.
```

## Priority ranking

| Priority | Dual Optic | Operation | Containers | Value |
|----------|-----------|-----------|------------|-------|
| **High** | Cxsetter | `filterWithKey`, `mapMaybeWithKey` | Map, HashMap | New capability |
| **High** | Cxfold | `foldMapWithKey`, `foldrWithKey` | Map, HashMap | Completes the Cx story |
| **Medium** | Cotraversal | `zipWith`, `intersectionWith` | Seq, Map, HashMap | Extends zip surface |
| **Medium** | Sort merge | `unionWithKey`, `intersectionWithKey` | HashMap | Parity with Map |
| **Low** | Cosort | keyed construction | Map, HashMap | Mostly structural |
| **Low** | Cofold | `foldTree` | Tree | Recursive, needs special handling |
| **Low** | ContJoin | CPS folds | any | Theoretical value |

## Vector

Vector has the richest indexed API of any Haskell container — every
major operation has an `i`-prefixed variant.

### Cxsetter — indexed vector operations

```haskell
-- Vector.imap :: (Int -> a -> b) -> v a -> v b
-- Already capturable as: cxsets cxmapped
-- But a dedicated optic composes better.

-- Vector.ifilter :: (Int -> a -> Bool) -> v a -> v a
cxfiltered :: Cxsetter Int (v a) (v a) a Bool

-- Vector.imapMaybe :: (Int -> a -> Maybe b) -> v a -> v b
cxmapMaybed :: Cxsetter Int (v a) (v b) a (Maybe b)
```

### Cotraversal — zipping

```haskell
-- Vector.zipWith :: (a -> b -> c) -> v a -> v b -> v c
-- Vector.izipWith :: (Int -> a -> b -> c) -> v a -> v b -> v c
--
-- These are binary cotraversals: combine two containers pointwise.
-- The indexed variants add Cx threading.
```

### Colens — generate / backpermute

```haskell
-- Vector.generate :: Int -> (Int -> a) -> v a
-- "A vector IS a function from indices" — same pattern as zipsMap.

grateVec :: Int -> Colens (v a) (v b) (Int -> a) (Int -> b)

-- Vector.backpermute :: v a -> v Int -> v a
-- "Apply a permutation to a vector" — consumes an index function.
-- This is a Colens where the "function" is the permutation vector.
```

### Cxfold — indexed folds

```haskell
-- Vector.ifoldl' :: (a -> Int -> b -> a) -> a -> v b -> a
-- Vector.ifoldr  :: (Int -> a -> b -> b) -> b -> v a -> b
-- Same shapes as Map.foldlWithKey / foldrWithKey.
```

### Scanning — stateful cotraversal

```haskell
-- Vector.iscanl' :: (Int -> a -> b -> a) -> a -> v b -> v a
-- Vector.iscanr  :: (Int -> a -> b -> b) -> b -> v a -> v b
--
-- Scans are "cotraversals with memory" — they produce a container
-- of intermediate fold results. The indexed variants thread the
-- position. These could be Cxcotraversals if we had state threading.
```

### constructN — self-referential construction

```haskell
-- Vector.constructN :: Int -> (v a -> a) -> v a
--
-- Builds a vector where each element depends on the previously
-- built prefix. This is a genuinely novel shape:
-- (v a -> a) -> v a
-- It's a coalgebra / corecursive unfold. Could be a Colens where
-- the "function" is the constructor and the "container" is the
-- growing vector.
```

## Text

Text is monomorphic (`Char`), so dual optics are less polymorphic.
The main interest is in scanning, accumulation, and breaking.

### Cosetter — map with accumulation

```haskell
-- Text.mapAccumL :: (a -> Char -> (a, Char)) -> a -> Text -> (a, Text)
-- Text.mapAccumR :: (a -> Char -> (a, Char)) -> a -> Text -> (a, Text)
--
-- These are "stateful cosetters" — they transform elements while
-- threading an accumulator. The shape (a -> Char -> (a, Char)) is
-- a state-passing SEC.
```

### Cotraversal — zipWith

```haskell
-- Text.zipWith :: (Char -> Char -> Char) -> Text -> Text -> Text
--
-- Binary cotraversal, same pattern as vector/sequence zips.
```

### Colens — unfold as dual of fold

```haskell
-- Text.unfoldr  :: (a -> Maybe (Char, a)) -> a -> Text
-- Text.unfoldrN :: Int -> (a -> Maybe (Char, a)) -> a -> Text
--
-- The unfold/fold duality: unfoldr is a coalgebra producing Text,
-- foldr is an algebra consuming Text. These form an adjoint pair
-- at the operational level.
```

### Scanning

```haskell
-- Text.scanl  :: (Char -> Char -> Char) -> Char -> Text -> Text
-- Text.scanl1 :: (Char -> Char -> Char) -> Text -> Text
-- Text.scanr  :: (Char -> Char -> Char) -> Char -> Text -> Text
-- Text.scanr1 :: (Char -> Char -> Char) -> Text -> Text
--
-- Same "cotraversal with memory" pattern as vector scans.
```

### Breaking / splitting — traversal0-like

```haskell
-- Text.break    :: (Char -> Bool) -> Text -> (Text, Text)
-- Text.span     :: (Char -> Bool) -> Text -> (Text, Text)
-- Text.breakOn  :: Text -> Text -> (Text, Text)
-- Text.split    :: (Char -> Bool) -> Text -> [Text]
-- Text.splitOn  :: Text -> Text -> [Text]
--
-- These decompose Text into parts. The predicate-based ones
-- (break, span, split) consume a function to decide where to cut.
-- Not standard dual optics, but the pattern of "consuming a
-- predicate to produce a decomposition" is Costar-flavored.
```

## ByteString

ByteString mirrors Text closely (monomorphic in `Word8`).
Same dual optic shapes apply.

### Cosetter — map with accumulation

```haskell
-- BS.mapAccumL :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
-- BS.mapAccumR :: (acc -> Word8 -> (acc, Word8)) -> acc -> ByteString -> (acc, ByteString)
```

### Cotraversal — packZipWith

```haskell
-- BS.packZipWith :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString -> ByteString
--
-- Unlike Text.zipWith which returns Text, this stays in ByteString.
-- Clean binary cotraversal.
```

### Colens — unfolding

```haskell
-- BS.unfoldr  :: (a -> Maybe (Word8, a)) -> a -> ByteString
-- BS.unfoldrN :: Int -> (a -> Maybe (Word8, a)) -> a -> (ByteString, Maybe a)
--
-- Same fold/unfold duality as Text.
```

### Scanning

```haskell
-- BS.scanl1 :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString
-- BS.scanr1 :: (Word8 -> Word8 -> Word8) -> ByteString -> ByteString
--
-- Note: no scanl/scanr (non-1 variants) in ByteString.
```

## Cross-cutting patterns

### Pattern 1: Indexed operations (Cxsetter/Cxfold)

Every container with positions has `*WithKey`/`i*` operations:

| Library | map | filter | fold | traverse |
|---------|-----|--------|------|----------|
| Map | `mapWithKey` | `filterWithKey` | `foldMapWithKey` | `traverseWithKey` |
| HashMap | `mapWithKey` | `filterWithKey` | `foldMapWithKey` | `traverseWithKey` |
| IntMap | `mapWithKey` | `filterWithKey` | `foldMapWithKey` | `traverseWithKey` |
| Vector | `imap` | `ifilter` | `ifoldl'`/`ifoldr` | `itraverse` |
| Seq | `mapWithIndex` | — | `foldlWithIndex` | `traverseWithIndex` |

All of these should have Cx duals.

### Pattern 2: Zip/pointwise operations (Cotraversal)

| Library | zipWith | indexed zipWith |
|---------|---------|-----------------|
| Vector | `zipWith` (up to 6-ary) | `izipWith` (up to 6-ary) |
| Seq | `zipWith` (up to 4-ary) | — |
| Text | `zipWith` | — |
| ByteString | `packZipWith` | — |
| Map | `intersectionWith` | `intersectionWithKey` |
| HashMap | `intersectionWith` | `intersectionWithKey` |

### Pattern 3: Generate/construct from function (Colens)

| Library | generate | from keys |
|---------|----------|-----------|
| Vector | `generate :: Int -> (Int -> a) -> v a` | `backpermute` |
| Map | — | `fromSet :: (k -> a) -> Set k -> Map k a` |
| Seq | — | — |
| Text | `unfoldr` | — |
| ByteString | `unfoldr` | — |

### Pattern 4: Accumulating map (Cosetter with state)

| Library | mapAccumL | mapAccumR |
|---------|-----------|-----------|
| Map | `mapAccumWithKey` | `mapAccumRWithKey` |
| Vector | — (via `mapAccumL` from Data.List) | — |
| Text | `mapAccumL` | `mapAccumR` |
| ByteString | `mapAccumL` | `mapAccumR` |
| Seq | — | — |

### Pattern 5: Scanning (Cotraversal with memory)

| Library | scanl | indexed scanl |
|---------|-------|---------------|
| Vector | `scanl`/`scanl'` (plus pre/post variants) | `iscanl`/`iscanl'` |
| Text | `scanl`/`scanl1` | — |
| ByteString | `scanl1` | — |
| Map | — | — |
| Seq | — | — |

## Updated priority ranking

| Priority | Dual Optic | Operations | Libraries | Value |
|----------|-----------|------------|-----------|-------|
| **High** | Cxsetter | `*WithKey`, `imap`, `ifilter`, `imapMaybe` | All keyed | Completes Cx story |
| **High** | Cxfold | `fold*WithKey`, `ifoldl'`, `ifoldr` | All keyed | Completes Cx story |
| **High** | Cotraversal | `zipWith`, `izipWith`, `intersectionWith`, `packZipWith` | Vector, Map, HashMap, BS | Pointwise zipping |
| **Medium** | Colens | `generate`, `backpermute`, `fromSet` | Vector, Map | Function-as-container |
| **Medium** | Sort merge | `unionWithKey`, `intersectionWithKey`, `differenceWithKey` | HashMap | Parity with Map |
| **Medium** | Cosetter | `mapAccumL`, `mapAccumR`, `mapAccumWithKey` | Map, Text, BS | Stateful transform |
| **Low** | Cxcotraversal | `iscanl'`, `iscanr` | Vector | Indexed scanning |
| **Low** | Cosort | keyed construction | Map, HashMap | Structural |
| **Low** | ContJoin | CPS folds | any | Theoretical |

## What's missing vs what's already there

The main gap: **the Cx (coindexed) story is incomplete across all
container types.** The library has `ixmapped`, `ixfolded`,
`ixtraversed`, `ixfiltered` for Map/IntMap/Seq/List. The Cx duals
are mostly absent. Vector's rich `i*` API is entirely uncovered.

The Colens surface is well-covered for containers (`zipsMap` etc.)
but absent for Vector (`generate`, `backpermute`).

The Cotraversal surface (zipping) has `coliftedA`/`zipListed` for
lists but nothing for Vector, Seq, Map intersection, or
Text/ByteString `zipWith`.

The Cosetter surface for stateful operations (`mapAccumL` etc.) is
completely uncovered.

Vector is the highest-value target for new container optic modules
due to its rich indexed API and the absence of any current coverage.

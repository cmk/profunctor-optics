# Map.Optic coverage vs Data.Map API

## Legend

- Y = covered by existing optic
- P = partially covered (e.g. only Ix, not Cx)
- - = not applicable (no natural optic shape)
- **MISS** = should have an optic but doesn't

## Query

| containers | Type | Optic | Status |
|-----------|------|-------|--------|
| `lookup` | `k -> Map k a -> Maybe a` | `at` (Traversal0') | Y |
| `(!)` | `Map k a -> k -> a` | — (partial, unsafe) | - |
| `(!?)` | `Map k a -> k -> Maybe a` | `at` | Y |
| `member` | `k -> Map k a -> Bool` | — (Bool query) | - |
| `notMember` | `k -> Map k a -> Bool` | — | - |
| `findWithDefault` | `a -> k -> Map k a -> a` | — (defaulting query) | - |
| `lookupLT` | `k -> Map k v -> Maybe (k,v)` | `lookedLT` (Ixtraversal0') | Y |
| `lookupGT` | `k -> Map k v -> Maybe (k,v)` | `lookedGT` | Y |
| `lookupLE` | `k -> Map k v -> Maybe (k,v)` | `lookedLE` | Y |
| `lookupGE` | `k -> Map k v -> Maybe (k,v)` | `lookedGE` | Y |
| `size` | `Map k a -> Int` | — (scalar query) | - |
| `null` | `Map k a -> Bool` | — | - |
| `lookupIndex` | `k -> Map k a -> Maybe Int` | — (index query) | - |
| `findIndex` | `k -> Map k a -> Int` | — | - |
| `lookupMin` | `Map k a -> Maybe (k,a)` | `lookedMin` (Ixfold0) | Y |
| `lookupMax` | `Map k a -> Maybe (k,a)` | `lookedMax` (Ixfold0) | Y |
| `findMin` | `Map k a -> (k,a)` | — (partial) | - |
| `findMax` | `Map k a -> (k,a)` | — (partial) | - |

## Insert / Delete / Update (single key)

| containers | Type | Optic | Status |
|-----------|------|-------|--------|
| `insert` | `k -> a -> Map k a -> Map k a` | `altered` (Setter) | Y |
| `insertWith` | `(a->a->a) -> k -> a -> Map -> Map` | — (combining insert) | - |
| `insertWithKey` | `(k->a->a->a) -> k -> a -> Map -> Map` | — | - |
| `insertLookupWithKey` | `... -> (Maybe a, Map k a)` | — | - |
| `delete` | `k -> Map k a -> Map k a` | `altered` (set to Nothing) | Y |
| `adjust` | `(a->a) -> k -> Map -> Map` | `adjusted` (Ixsetter') | Y |
| `adjustWithKey` | `(k->a->a) -> k -> Map -> Map` | `adjusted` | Y |
| `update` | `(a -> Maybe a) -> k -> Map -> Map` | `updated` (Ixsetter) | Y |
| `updateWithKey` | `(k->a->Maybe a) -> k -> Map -> Map` | `updated` | Y |
| `updateLookupWithKey` | `... -> (Maybe a, Map k a)` | `updateLooked` (Ixsetter) | Y |
| `alter` | `(Maybe a -> Maybe a) -> k -> Map -> Map` | `altered` (Setter') | Y |
| `alter'` (strict) | same | `altered'` | Y |
| `alterF` | `Functor f => (Maybe a -> f (Maybe a)) -> ...` | `alteredF` (Lens') | Y |
| `upsert` | `(Maybe a -> a) -> k -> Map -> Map` | — | **MISS** |
| `pop` | `k -> Map k a -> Maybe (a, Map k a)` | — | **MISS** |

## Traverse / Map

| containers | Type | Optic | Status |
|-----------|------|-------|--------|
| `map` | `(a->b) -> Map k a -> Map k b` | `mapped` (Setter) | Y |
| `mapWithKey` | `(k->a->b) -> Map k a -> Map k b` | `ixmapped` (Ixsetter), `cxmapped` (Cxsetter) | Y |
| `traverseWithKey` | `Applicative t => (k->a->t b) -> ...` | `ixtraversed` (Ixtraversal), `cxtraversed` (Cxtraversal) | Y |
| `traverseMaybeWithKey` | `Applicative f => (k->a->f (Maybe b)) -> ...` | — | **MISS** |
| `mapAccum` | `(a->b->(a,c)) -> a -> Map k b -> (a, Map k c)` | — (stateful) | - |
| `mapAccumWithKey` | `(a->k->b->(a,c)) -> a -> Map k b -> (a, Map k c)` | — (stateful) | - |
| `mapAccumRWithKey` | same, right-to-left | — | - |
| `mapKeys` | `(k1->k2) -> Map k1 a -> Map k2 a` | — (key transform) | **MISS** |
| `mapKeysWith` | `(a->a->a) -> (k1->k2) -> Map k1 a -> Map k2 a` | — | - |
| `mapKeysMonotonic` | `(k1->k2) -> Map k1 a -> Map k2 a` | — | **MISS** |

## Filter

| containers | Type | Optic | Status |
|-----------|------|-------|--------|
| `filter` | `(a->Bool) -> Map k a -> Map k a` | — (no key) | **MISS** |
| `filterWithKey` | `(k->a->Bool) -> Map k a -> Map k a` | `ixfiltered` (Ixsetter), `cxfiltered` (Cxsetter) | Y |
| `filterKeys` | `(k->Bool) -> Map k a -> Map k a` | — (key-only filter) | **MISS** |
| `partition` | `(a->Bool) -> Map -> (Map, Map)` | — (pair result) | - |
| `partitionWithKey` | `(k->a->Bool) -> Map -> (Map, Map)` | — | - |
| `mapMaybe` | `(a -> Maybe b) -> Map k a -> Map k b` | — (no key) | **MISS** |
| `mapMaybeWithKey` | `(k->a->Maybe b) -> Map k a -> Map k b` | `cxmappedIf` (Cxsetter) | P (Cx only) |
| `mapEither` | `(a -> Either b c) -> Map -> (Map, Map)` | — | - |
| `mapEitherWithKey` | `(k->a->Either b c) -> Map -> (Map, Map)` | — | - |
| `takeWhileAntitone` | `(k->Bool) -> Map -> Map` | — | - |
| `dropWhileAntitone` | `(k->Bool) -> Map -> Map` | — | - |
| `spanAntitone` | `(k->Bool) -> Map -> (Map, Map)` | — | - |

## Fold

| containers | Type | Optic | Status |
|-----------|------|-------|--------|
| `foldr` | `(a->b->b) -> b -> Map k a -> b` | `values` (Fold) | Y |
| `foldl'` | `(a->b->a) -> a -> Map k b -> a` | `values` | Y |
| `foldrWithKey` | `(k->a->b->b) -> b -> Map k a -> b` | `ixfolded` (Ixfold), `cxfolded` (Cxfold) | Y |
| `foldlWithKey'` | `(a->k->b->a) -> a -> Map k b -> a` | `ixfolded`, `cxfolded` | Y |
| `foldMapWithKey` | `Monoid m => (k->a->m) -> Map k a -> m` | `ixfolded`, `cxfolded` | Y |

## Construction from keys

| containers | Type | Optic | Status |
|-----------|------|-------|--------|
| `fromSet` | `(k->a) -> Set k -> Map k a` | `zipped` (Colens) | Y |
| `fromSetA` | `Applicative f => (k->f a) -> Set k -> f (Map k a)` | `zippedTraverse` (Cotraversal) | Y |
| `empty` | `Map k a` | — | - |
| `singleton` | `k -> a -> Map k a` | — | - |
| `fromList` | `[(k,a)] -> Map k a` | — | - |
| `fromListWith` | `(a->a->a) -> [(k,a)] -> Map k a` | — | - |

## Combine (binary)

| containers | Type | Optic | Status |
|-----------|------|-------|--------|
| `union` | `Map -> Map -> Map` | — | - |
| `unionWith` | `(a->a->a) -> Map -> Map -> Map` | — | - |
| `unionWithKey` | `(k->a->a->a) -> Map -> Map -> Map` | — | - |
| `intersection` | `Map k a -> Map k b -> Map k a` | — | - |
| `intersectionWith` | `(a->b->c) -> Map k a -> Map k b -> Map k c` | — | - |
| `intersectionWithKey` | `(k->a->b->c) -> ...` | — | - |
| `difference` | `Map k a -> Map k b -> Map k a` | — | - |
| `differenceWith` | `(a->b->Maybe a) -> ...` | — | - |
| `differenceWithKey` | `(k->a->b->Maybe a) -> ...` | — | - |
| `compose` | `Map b c -> Map a b -> Map a c` | — | - |
| `merge` | (tactic-based) | `merges` + `sortingMatched`/`sortingMissing` (operators) | Y |

## Indexed (positional)

| containers | Type | Optic | Status |
|-----------|------|-------|--------|
| `elemAt` | `Int -> Map k a -> (k,a)` | — | **MISS** |
| `updateAt` | `(k->a->Maybe a) -> Int -> Map -> Map` | — | **MISS** |
| `deleteAt` | `Int -> Map k a -> Map k a` | — | **MISS** |
| `take` | `Int -> Map k a -> Map k a` | — | **MISS** |
| `drop` | `Int -> Map k a -> Map k a` | — | **MISS** |
| `splitAt` | `Int -> Map -> (Map, Map)` | — | **MISS** |

## Split

| containers | Type | Optic | Status |
|-----------|------|-------|--------|
| `split` | `k -> Map -> (Map, Map)` | — | - |
| `splitLookup` | `k -> Map -> (Map, Maybe a, Map)` | — | - |

## Min/Max update

| containers | Type | Optic | Status |
|-----------|------|-------|--------|
| `deleteMin`/`deleteMax` | `Map -> Map` | — | - |
| `updateMin`/`updateMax` | `(a->Maybe a) -> Map -> Map` | — | **MISS** |
| `updateMinWithKey`/`updateMaxWithKey` | `(k->a->Maybe a) -> Map -> Map` | — | **MISS** |
| `minView`/`maxView` | `Map -> Maybe (a, Map)` | — | **MISS** |
| `minViewWithKey`/`maxViewWithKey` | `Map -> Maybe ((k,a), Map)` | — | **MISS** |

## Summary of gaps

### High value (natural optic shape)

1. **`filter`** — non-keyed filter: `Setter' (Map k a) (Map k a) a Bool` (no key param, unlike `filterWithKey`)
2. **`mapMaybe`** — non-keyed mapMaybe: `Setter (Map k a) (Map k b) a (Maybe b)`
3. **`mapKeys`/`mapKeysMonotonic`** — key transformation setter
4. **`traverseMaybeWithKey`** — keyed traversal+filter
5. **`elemAt`** — positional access by Int index (like `at` but by position)
6. **`updateMin`/`updateMax`** — min/max update setters

### Medium value

7. **`upsert`** — insert-or-update
8. **`pop`** — delete and return
9. **`take`/`drop`/`splitAt`** — positional splitting
10. **`minView`/`maxView`** — min/max view+delete

### Not natural optic shapes

- `partition`/`mapEither` — produce pairs of maps (not a single focus)
- `union`/`intersection`/`difference` — binary operators, already covered by `merges`
- `mapAccum*` — sequential state threading
- `takeWhileAntitone`/`dropWhileAntitone` — key-monotonic operations
- Scalar queries (`null`, `size`, `member`)
- Construction (`empty`, `singleton`, `fromList`)

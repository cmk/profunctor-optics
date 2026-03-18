# profunctor-optics-containers

Profunctor optics for `containers` types: `Map`, `IntMap`, `Set`,
`IntSet`, `Seq`, `Tree`, and `List`.

## Overview

This package provides two layers of access to container types:

1. **Key-value optics** — `at`, `itraversed`, `ifolded`, etc.
   for working with container elements via their keys
2. **Structural pattern functors** — `MapF`, `IntMapF`, `SetF`,
   `IntSetF` for recursion-scheme access to the internal BST
   tree structure

The key-value optics are the standard user-facing API. The
pattern functors enable advanced structural operations
(tree depth, balance analysis, structural transformations)
via `scheme-extensions`.

## Indexed optics

### Theory

An **indexed optic** threads an index alongside the value
at each focus. In profunctor optics, this is represented
by the `Ixoptic` family:

```
Ixtraversal k s t a b = forall p. (Strong p, Traversing p) => Ixoptic p k s t a b
```

The index `k` is typically the key type of the container.
Indexed optics compose — when you compose two indexed optics,
the indices compose too (via `Semigroup`).

### Simple example: indexed map traversal

```haskell
import Data.Map.Optic
import Data.Profunctor.Optic
import qualified Data.Map as Map

-- itraversed gives key-value access:
>>> iover itraversed (\k v -> show k ++ ":" ++ v) (Map.fromList [(1,"a"),(2,"b")])
fromList [(1,"1:a"),(2,"2:b")]

-- ifolded collapses with keys:
>>> ilists ifolded (Map.fromList [(1,"hello"),(2,"world")])
[(1,"hello"),(2,"world")]
```

### Complex example: filtered update with index

```haskell
import Data.Map.Optic
import Data.Profunctor.Optic
import qualified Data.Map as Map

-- Only adjust values at even keys:
>>> iover (adjusted 2) (\k v -> v ++ "!") (Map.fromList [(1,"a"),(2,"b"),(3,"c")])
fromList [(1,"a"),(2,"b!"),(3,"c")]

-- Alter with index-dependent logic:
>>> let f k _ = if even k then Just "even" else Nothing
>>> iover (ialtered 2) f (Map.fromList [(1,"a"),(2,"b")])
fromList [(1,"a"),(2,"even")]
>>> iover (ialtered 1) f (Map.fromList [(1,"a"),(2,"b")])
fromList [(2,"b")]
```

## Co-indexed optics

### Theory

A **co-indexed optic** (or **cxoptic**) threads an index
on the *co*-side — the reconstruction/setter side rather
than the getter/fold side. Where an indexed traversal tells
you "this value was at key `k`", a co-indexed cotraversal
tells you "reconstruct using index `k`".

```
Cxtraversal k s t a b = forall p. (Closed p, Cotraversing p) => Cxoptic p k s t a b
```

Co-indexed optics are less common but arise naturally when
working with cotraversals and grates, which operate on the
dual (reconstruction) side.

### Simple example: co-indexed setter

```haskell
import Data.Map.Optic
import Data.Profunctor.Optic
import qualified Data.Map as Map

-- imapped provides index-aware setting:
>>> iover imapped (\k v -> v + k) (Map.fromList [(1,10),(2,20),(3,30)])
fromList [(1,11),(2,22),(3,33)]
```

## Affine optics (partial access)

### Theory

An **affine traversal** (`Traversal0`) focuses on zero or one
element — like a `Lens` that might not be there:

```
Traversal0 s t a b = forall p. (Strong p, Choice p) => p a b -> p s t
```

Map's `at` is the canonical example: the value at a given
key might or might not exist.

### Simple example: at a key

```haskell
import Data.Map.Optic
import Data.Profunctor.Optic
import qualified Data.Map as Map

>>> Map.fromList [(1,"hello")] ^. at 1
"hello"
>>> Map.fromList [(1,"hello")] ^. at 2
""
>>> Map.fromList [(1,'a')] & at 1 ..~ toUpper
fromList [(1,'A')]
```

### Complex example: nested map access

```haskell
import Data.Map.Optic
import Data.Profunctor.Optic
import qualified Data.Map as Map

-- Compose at to access nested maps:
type DB = Map.Map String (Map.Map String Int)

-- Access a specific nested value:
>>> let db = Map.fromList [("users", Map.fromList [("alice",1),("bob",2)])]
>>> db ^. at "users" . at "alice"
-- (requires appropriate Monoid instance)
```

## Structural optics (via pattern functors)

### Theory

The internal BST structure of `Map`, `IntMap`, `Set`, and
`IntSet` can be exposed via **pattern functors** — one-layer
views of the recursive tree structure:

```haskell
data MapF k v r = MapTip | MapBin !Size !k v r r
data SetF a r   = SetTip | SetBin !Size !a r r
```

Combined with `Mu` (Church-encoded fixed point) and recursion
schemes from `scheme-extensions`, these enable structural
operations not expressible via the standard container API.

```
Map k v  ≅  Mu (MapF k v)    -- via toMapF / fromMapF
IntMap a ≅  Mu (IntMapF a)
Set a    ≅  Mu (SetF a)
IntSet   ≅  Mu IntSetF
```

### Simple example: tree depth

```haskell
import Data.Map.Optic
import qualified Data.Map as Map

-- Compute BST depth (not possible with standard Map API):
>>> depth (Map.fromList [(1,'a'),(2,'b'),(3,'c'),(4,'d'),(5,'e')])
3
>>> depth Map.empty
0
```

### Complex example: structural analysis

```haskell
import Data.Map.Optic
import Data.Container.Pattern
import Data.Functor.Foldable (fold, refold)
import qualified Data.Map as Map

-- Collect all sizes at internal nodes:
>>> sizes (Map.fromList [(1,'a'),(2,'b'),(3,'c')])
[3,1,1]

-- Round-trip through pattern functor (identity):
>>> let m = Map.fromList [(1,"hello"),(2,"world")]
>>> rebalanced m == m
True

-- Use refold for structure-to-structure transformation
-- (e.g., Map → IntMap) without materializing intermediate Mu:
mapToIntMap :: Map.Map Int v -> IntMap.IntMap v
mapToIntMap = refold intmapAlg mapCoalg
  where
    mapCoalg = ... -- project Map into MapF
    intmapAlg = ... -- embed IntMapF into IntMap
```

## Modules

| Module | Contents |
|---|---|
| `Data.Container.Pattern` | `MapF`, `IntMapF`, `SetF`, `IntSetF` pattern functors + `to*`/`from*` conversions |
| `Data.Map.Optic` | `at`, `iat`, `values`, `imapped`, `ifiltered`, `itraversed`, `ifolded`, `altered`, `ialtered`, `alteredF`, `ialteredF`, `adjusted`, `updated`, `updateLooked`, `lookedMin`/`Max`/`LT`/`LE`/`GE`/`GT`, `validated`, `depth`, `sizes`, `rebalanced` |
| `Data.Map.NonEmpty.Optic` | Optics for non-empty maps |
| `Data.List.Optic` | List optics |
| `Data.Sequence.Optic` | Sequence optics (`slicedTo`, etc.) |
| `Data.Tree.Optic` | Tree optics (`root`, etc.) |

## Dependencies

```
base, containers, nonempty-containers, profunctor-optics, scheme-extensions
```

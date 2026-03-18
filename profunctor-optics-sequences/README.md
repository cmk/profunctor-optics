# profunctor-optics-sequences

Profunctor optics for `MonoTraversable` sequence types.

## Overview

This package provides sequence-level optics built on
`mono-traversable`: packing, chunking, filtering, splitting,
and pattern synonyms for strict/lazy/chunked/reversed
representations.

**Note:** For `ByteString` and `Text` specifically, consider
using `profunctor-optics-strings` instead, which provides
the same functionality via cotraversals and isos without
the `mono-traversable` dependency.

## Sequence optics

### Theory

`MonoTraversable` generalizes `Traversable` to types with
a single element type (monomorphic containers like
`ByteString`, `Text`, `Vector`, etc.):

```haskell
class MonoFunctor mono => MonoTraversable mono where
    otraverse :: Applicative f => (Element mono -> f (Element mono)) -> mono -> f mono
```

This package lifts `MonoTraversable` operations into
profunctor optics.

### Simple example: packing and chunking

```haskell
import Data.Profunctor.Optic.Sequence
import Data.Profunctor.Optic

-- Pack a list into a sequence type:
>>> view packing [72, 101, 108, 108, 111] :: ByteString
"Hello"

-- Chunk a lazy type into strict chunks:
>>> view chunking ("hello world" :: BL.ByteString) :: [ByteString]
["hello world"]
```

### Complex example: filtered splitting

```haskell
import Data.Profunctor.Optic.Sequence
import Data.Profunctor.Optic

-- Take while a predicate holds:
>>> view (takenWhile (< 5)) [1, 2, 3, 6, 7, 8] :: [Int]
[1, 2, 3]

-- Drop while a predicate holds:
>>> view (droppedWhile (< 5)) [1, 2, 3, 6, 7, 8] :: [Int]
[6, 7, 8]

-- Filter by a predicate:
>>> view (filteredBy even) [1, 2, 3, 4, 5, 6] :: [Int]
[2, 4, 6]

-- Split on a predicate:
>>> view (broken (> 3)) [1, 2, 3, 4, 5] :: ([Int], [Int])
([1, 2, 3], [4, 5])

-- Partition by a predicate:
>>> view (partitioned even) [1, 2, 3, 4, 5] :: ([Int], [Int])
([2, 4], [1, 3, 5])
```

## Pattern synonyms

### Theory

Pattern synonyms provide bidirectional access to
representations — you can both match and construct
via the pattern.

### Simple example: strict/lazy conversion

```haskell
import Data.Profunctor.Optic.Pattern

-- View as strict or lazy:
>>> review Lazy ("hello" :: ByteString) :: BL.ByteString
"hello"
>>> review Strict ("hello" :: BL.ByteString) :: ByteString
"hello"

-- Reversed view:
>>> review Reversed [1, 2, 3]
[3, 2, 1]
```

## Co-traversals and duality

### Theory

Where `filteredBy` and `takenWhile` are traversal-like
(they select elements), their duals would be cotraversal-like
(they reconstruct from observations). The `'` variants in
this package often represent the dual perspective:

```haskell
taken  :: ... -> Traversal' s s  -- take from the front
taken' :: ... -> Resetter' s s   -- reset/rebuild the front
```

`Resetter` is the dual of `Setter` — where a setter modifies
elements one at a time, a resetter reconstructs the whole
container.

### Simple example: padded (dual of taken)

```haskell
import Data.Profunctor.Optic.Sequence

-- padded extends a sequence to a minimum length:
>>> view (padded 5 0) [1, 2, 3] :: [Int]
[1, 2, 3, 0, 0]
```

## Modules

| Module | Contents |
|---|---|
| `Data.Profunctor.Optic.Sequence` | `strict`, `chunked`, `unpacked`, `reversed`, `packing`, `chunking`, `packed`, `taken`, `takenWhile`, `droppedWhile`, `filteredBy`, `broken`, `spanned`, `partitioned`, `splitWhen`, `splitFirst`, `obuildl`, etc. |
| `Data.Profunctor.Optic.Pattern` | `Lazy`, `Strict`, `Chunked`, `Packed`, `Unpacked`, `Swapped`, `Reversed` pattern synonyms |

## Dependencies

```
base, mono-traversable, profunctor-optics, profunctor-optics-folds, semigroupoids
```

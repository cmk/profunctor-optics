[![Haddocks](https://img.shields.io/badge/docs-haddocks-blue)](https://cmk.github.io/profunctor-optics/profunctor-optics-strings/)
[![CI](https://github.com/cmk/profunctor-optics/actions/workflows/ci.yml/badge.svg)](https://github.com/cmk/profunctor-optics/actions/workflows/ci.yml)

# profunctor-optics-strings

Profunctor optics for string-like types: `ByteString`, `Text`,
and fixed-width `Word` types.

## Overview

This package provides five families of optics:

1. **Bit-level cotraversals** (`bits8`..`bits64`) — view a
   `Word` as N bits via `Distributive`
2. **Indexed bit-level cotraversals** (`ibits8`..`ibits64`) —
   same, but the bit position is available as an index (6–7x
   faster than non-indexed)
3. **Grates** (`grate8`..`grate64`) — colenses for pointwise
   zipping of `Word` types via `zipsWith`
4. **Splitting isos** (`lined`, `worded`, `splitOn`) — zero-cost
   wrappers around `ByteString`/`Text` splitting functions
5. **Representation isos** — strict ↔ lazy, packed, short, `utf8`

These compose with the full `profunctor-optics` hierarchy. The
bit-level optics use index types from `scheme-extensions` to make
`(->) IN` a `Distributive` functor.

## Cotraversals (dual of traversals)

### Theory

A **traversal** lets you visit each element of a container:

```
Traversal s t a b = forall p. (Strong p, Traversing p) => p a b -> p s t
```

A **cotraversal** is the dual — it lets you reconstruct a
container from observations of all its elements simultaneously:

```
Cotraversal s t a b = forall p. (Closed p, Cotraversing p) => p a b -> p s t
```

Where a traversal uses `Traversable` (sequential access),
a cotraversal uses `Distributive` (simultaneous observation).
A `Distributive` functor is one where you can "distribute"
any functor through it — the dual of `Traversable`.

### Example 1: flip all bits

```haskell
import Data.Word.Optic
import Data.Profunctor.Optic

-- Word8 ≅ (I8 -> Bool), so bits8 is a cotraversal
-- over all 8 bit positions simultaneously.

>>> over bits8 not 0xFF
0
>>> over bits8 not 0x00
255
>>> over bits8 id 42
42
```

`over bits8 f` applies `f` to each bit position of the `Word8`
and reconstructs the result. Since all bits are observed
simultaneously (not sequentially), this is a cotraversal,
not a traversal.

### Example 2: bit manipulation pipeline

```haskell
import Data.Word.Optic
import Data.ByteString.Optic
import Data.Text.Optic
import Data.Profunctor.Optic

-- Compose isos to build a pipeline:
-- String → Text → ByteString → ShortByteString
utf8Pipeline :: Iso' String ShortByteString
utf8Pipeline = re packed . utf8 . short

-- Flip specific bits in a Word8 using the cotraversal
-- with a position-dependent function:
selectiveBits :: Word8 -> Word8
selectiveBits = over bits8 $ \b -> case b of
    True  -> False  -- clear set bits
    False -> True   -- set cleared bits
-- (this is just `complement`, but demonstrates the point)
```

## Indexed cotraversals (dual of indexed traversals)

### Theory

An **indexed traversal** lets you visit each element along
with its position:

```
Ixtraversal k s t a b = forall p. Traversing p => Ixoptic p k s t a b
```

An **indexed cotraversal** (or **cxlens**) is the dual — it
reconstructs a container from position-aware observations:

```
Cxlens k s t a b = forall p. Closed p => Cxoptic p k s t a b
```

It is characterized by:

```
cxlens :: (((s -> a) -> k -> b) -> t) -> Cxlens k s t a b
```

The key difference from a plain cotraversal: the reconstruction
function receives the index `k` (the bit position) alongside the
extractor `(s -> a)`. This lets you write position-dependent logic
without decomposing into individual elements.

### Example 1: position-aware bit flipping

```haskell
import Data.Word.Optic
import Data.Profunctor.Optic

-- ibits8 is an indexed cotraversal: the index is the bit position (I8).
-- Flip only even-positioned bits:
>>> reoverWithKey ibits8 (\i b -> if even (fromEnum i) then not b else b) 0xFF
0xAA
```

### Example 2: conditional masking

```haskell
import Data.Word.Optic
import Data.Profunctor.Optic

-- Clear the high nibble, keep the low nibble:
clearHigh :: Word8 -> Word8
clearHigh = reoverWithKey ibits8 $ \i b ->
    if fromEnum i >= 4 then False else b

>>> clearHigh 0xFF
0x0F

-- Set bit N to True iff N is prime:
primeMask :: Word8
primeMask = reoverWithKey ibits8 (\i _ -> fromEnum i `elem` [1,2,4]) 0x00
```

## Grates (colenses)

### Theory

A **grate** (also called a **colens**) is an optic that gives
you the "environment" view of a container:

```
Colens s t a b = forall p. Closed p => p a b -> p s t
```

It is characterized by:

```
grate :: (((s -> a) -> b) -> t) -> Colens s t a b
```

Where a lens gives you `(s -> a, s -> b -> t)` (get + set),
a grate gives you `((s -> a) -> b) -> t` — "given any way
to observe `a` from `s`, produce a `b`, and I'll give you `t`".

Both cotraversals and grates are **O(n)** in the number of
elements — each bit position is visited exactly once during
reconstruction. Benchmarks confirm linear scaling: ~7 ns/bit
for indexed cotraversals, ~44 ns/bit for non-indexed, ~40 ns/bit
for grate `zipsWith`. The constant factor reflects the cost of
the `Bool`-level decomposition vs a single machine instruction.

The key operation on grates is `zipsWith`:

```
zipsWith :: AColens s t a b -> (a -> a -> b) -> s -> s -> t
```

This lets you combine two structures pointwise — a capability
that lenses and traversals lack.

### Example 1: grate8

```haskell
import Data.Word.Optic

-- grate8 views a Word8 through its I8 -> Bool representation.
-- The continuation receives toBits8, and you return a new
-- bit function to reconstruct.

>>> over grate8 id 42
42
>>> over grate8 (\bits -> \i -> not (bits i)) 0xFF
0
```

### Example 2: pointwise zipping and bit rotation

```haskell
import Data.Word.Optic
import Data.Functor.Index

-- zipsWith combines two Word8s pointwise through their
-- bit representations. Bool xor is (/=):
>>> zipsWith grate8 (liftA2 (/=)) 0xAA 0x55
0xFF

-- Rotate bits left by 1 position using the grate:
rotateLeft :: Word8 -> Word8
rotateLeft = over grate8 $ \bits ->
    \i -> bits (if i == I88 then I81 else succ i)
```

## Isos

### Theory

An **iso** (isomorphism) witnesses that two types are equivalent:

```
Iso s t a b = forall p. Profunctor p => p a b -> p s t
```

Isos compose in both directions — `view` goes one way,
`review` goes the other.

### Example 1: strict ↔ lazy ByteString

```haskell
import Data.ByteString.Optic
import Data.Profunctor.Optic

>>> view lazy ("hello" :: ByteString)
"hello"     -- :: BL.ByteString
>>> review lazy ("hello" :: BL.ByteString)
"hello"     -- :: ByteString
```

### Example 2: encode, pack, and shorten

```haskell
import Data.Text.Optic
import Data.ByteString.Optic
import Data.Profunctor.Optic

-- Compose isos: Text → ByteString → ShortByteString
textToShort :: Iso' Text ShortByteString
textToShort = utf8 . short

-- Or go the other way:
>>> review textToShort someShortBS  -- ShortByteString → Text
```

## Modules

| Module | Contents |
|---|---|
| `Data.Word.Optic` | `bits8`..`64` (cotraversals), `ibits8`..`64` (indexed), `grate8`..`64` (colenses), index re-exports |
| `Data.ByteString.Optic` | `short`, `lazy`, `packed` (isos), `lined`, `worded`, `splitOn` (splitting), `bytes` (traversal) |
| `Data.Text.Optic` | `short`, `lazy`, `packed`, `utf8` (isos), `lined`, `worded`, `splitOn` (splitting), `chars` (traversal) |

## Benchmarks

Run with `cabal bench`.

### Splitting optics: zero-cost abstraction

The splitting isos (`lined`, `worded`, `splitOn`) are thin wrappers
around the underlying library functions. Criterion confirms **zero
overhead** — the optic version matches the direct call exactly:

| Operation | Optic | Direct | Ratio |
|---|---|---|---|
| `view lined` (BS, 100 lines) | 1.41 μs | 1.42 μs | **1.0x** |
| `view worded` (BS, 100 words) | 2.02 μs | 1.78 μs | 1.1x |
| `view lined` (Text, 100 lines) | 1.32 μs | 1.32 μs | **1.0x** |
| `view worded` (Text, 100 words) | 1.87 μs | 1.88 μs | **1.0x** |

### Coindexed > colens > cotraversal

Three optic types access the same bit structure with very
different performance. **Prefer `ibitsN` (coindexed) over
`grateN` (colens) over `bitsN` (cotraversal):**

| Optic | Type | 8-bit | 64-bit | ns/bit |
|---|---|---|---|---|
| `ibitsN` (cxlens) | Coindexed | 59 ns | 380 ns | **~7** |
| `grateN` (colens) | Closed | ~170 ns | — | **~21** |
| `bitsN` (cotraversal) | Cotraversing | 381 ns | 2.79 μs | **~44** |
| `complement` (baseline) | Machine insn | 7.5 ns | 7.5 ns | **O(1)** |

The `cxlens`-based `ibitsN` avoids the `Distributive`/`cotraversed`
overhead entirely — the index is delivered directly through the
grate continuation. The `grateN` colens path reconstructs via a
single grate callback (~21 ns/bit). The `bitsN` cotraversal goes
through `iso toBits fromBits . cotraversed`, which reconstructs
from the `Costar` representation (~44 ns/bit).

All three are **O(n)** in the number of bits. The constant
factor reflects the abstraction path:

- **`ibitsN`**: index threaded directly through grate continuation
  — no functor reconstruction, nearly zero overhead
- **`grateN`**: one grate callback per element — moderate overhead
- **`bitsN`**: full `Distributive`/`Costar` reconstruction per
  element — highest overhead

When composing with profunctor carriers (e.g. `SortF`), the
carrier adds zero additional overhead — the cost is entirely
from the optic. Benchmarks confirm `ibitsN` applied to `SortF`
(12 ns) matches bare carrier cost (11 ns), while `bitsN`
applied to `SortF` (1.07 μs) matches `bitsN` applied to raw
`Costar` (1.00 μs).

### Element traversals

The `bytes`/`chars` traversals use `re packed . traversed`, which
unpacks and repacks. This gives ~6x overhead vs the fused `BS.map`
/ `T.map` implementations (27 μs vs 4.8 μs for 1000 bytes).

## Dependencies

```
base, bytestring, text, text-short, profunctor-optics, scheme-extensions
```

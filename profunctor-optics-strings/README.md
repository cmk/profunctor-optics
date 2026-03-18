# profunctor-optics-strings

Profunctor optics for string-like types: `ByteString`, `Text`,
and fixed-width `Word` types.

## Overview

This package provides three families of optics:

1. **Bit-level cotraversals** for fixed-size `Word` types — view a
   `Word8` as 8 bits, a `Word16` as 16 bits, etc.
2. **Isos** between strict/lazy/short representations of
   `ByteString` and `Text`
3. **Encoding isos** — `utf8` for Text ↔ ByteString conversion

These compose with the full `profunctor-optics` hierarchy. The
bit-level cotraversals use index types from `scheme-extensions`
to make `(->) IN` a `Distributive` functor.

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

### Simple example: flip all bits

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

### Complex example: bit manipulation pipeline

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

### Simple example: grate8

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

### Complex example: bit rotation via grate

```haskell
import Data.Word.Optic
import Data.Functor.Index

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

### Simple example: strict ↔ lazy ByteString

```haskell
import Data.ByteString.Optic
import Data.Profunctor.Optic

>>> view lazy ("hello" :: ByteString)
"hello"     -- :: BL.ByteString
>>> review lazy ("hello" :: BL.ByteString)
"hello"     -- :: ByteString
```

### Complex example: encode, pack, and shorten

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
| `Data.Word.Optic` | `bits8`/`16`/`32`/`64` (cotraversals), `grate8` (colens), `I4`/`I8`/`I16`/`I32`/`I64` re-exports |
| `Data.ByteString.Optic` | `short` (↔ ShortByteString), `lazy` (↔ Lazy), `packed` (↔ [Word8]) |
| `Data.Text.Optic` | `short` (↔ ShortText), `lazy` (↔ Lazy Text), `packed` (↔ String), `utf8` (↔ ByteString) |

## Dependencies

```
base, bytestring, text, text-short, profunctor-optics, scheme-extensions
```

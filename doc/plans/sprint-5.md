# Sprint 5 — Remaining design space exploration

## Scope

Close out the remaining unexplored areas from the Sort design space:
ByteString/Text via Sort3, indexed+coindexed composition chains,
Rxlens/Rxprism on Sort3, and evaluate whether profunctor-optics-sequences
should drop mono-traversable in favor of direct vector/array optics.

## Rationale

The Sort design space coverage table has gaps: ByteString/Text as
Int-indexed representable types (same as Vector but for bytes/chars),
Sort3 + Rxlens/Rxprism (coindexed dual optics), and composition of
indexed + coindexed optics through a sort pipeline. These are the
natural next steps before we have full coverage. The sequences
redesign question determines whether the vector/array sprint builds
on mono-traversable or replaces it.

## Stories

| ID    | Module / target               | Description                                           |
|-------|-------------------------------|-------------------------------------------------------|
| S5.1  | Data.Profunctor.Optic.Sort    | ByteString sorting via Sort3 + mkSort3N               |
| S5.2  | Data.Profunctor.Optic.Sort    | Text sorting via Sort3 + mkSort3N                     |
| S5.3  | Test.Prop.Sort                | Sort3 + Rxlens (coindexed Costrong)                   |
| S5.4  | Test.Prop.Sort                | Sort3 + Rxprism (coindexed Cochoice, Monoid i)        |
| S5.5  | Test.Prop.Sort                | Indexed+coindexed composition chain test              |
| S5.6  | doc/designs                   | Evaluate mono-traversable vs direct optics for seqs   |
| S5.7  | Data.Profunctor.Sort          | Fmt-inspired: Category, bind, cat for Sort3            |
| S5.8  | Data.Profunctor.Sort          | Fmt-inspired: sort1, either1, maybe1 combinators       |

## New functions

### S5.1 — ByteString sorting

```haskell
-- | Sort a strict ByteString's bytes by key via Sort3.
sortingBytes :: Ord k
             => (Word8 -> k)
             -> ByteString -> Map k ByteString

-- | Group a strict ByteString's bytes by value.
groupingBytes :: ByteString -> Map Word8 ByteString
```

### S5.2 — Text sorting

```haskell
-- | Sort a strict Text's characters by key via Sort3.
sortingChars :: Ord k
             => (Char -> k)
             -> Text -> Map k Text
```

### S5.3–S5.4 — Rxlens/Rxprism tests

```haskell
-- Sort3 has Costrong: Rxlens (coindexed Relens) should compose
-- Sort3 has Cochoice (Monoid i): Rxprism (coindexed Reprism) should compose
```

### S5.5 — Indexed+coindexed chain

```haskell
-- Test: sortingIx ixlens composed with cosortingOf bits8
-- The index accumulates monoidally via (%)
```

### S5.6 — Sequences redesign evaluation

Write a design doc answering:
- Does mono-traversable add value over direct Vector/Array optics?
- Which sequence types benefit from Sort3 (representable by Int)?
- Should profunctor-optics-sequences be split: one package per
  container backend (vector, primitive, array)?

### S5.7 — Fmt-inspired Category and bind

Sort3 ≅ Costar (Sort3Corep i j k), and Fmt = Costar ((->) m).
Fmt has Category (multi-pass formatting via `(%)`), Arrow, and
bind. Explore whether Sort3 can get the same:

```haskell
-- | Category: compose two sort passes (sort by g, refine by f).
-- Analogous to discrimination's (<>) on Sort.
instance (...) => Category (Sort3 i j k) where ...

-- | Key-dependent refinement: inspect the accumulated key
-- and choose a different sort strategy.
bindSort3 :: Sort3 i j k a b -> (k -> Sort3 i j k a' a) -> Sort3 i j k a' b

-- | Fold multiple sort passes into one.
catSort3 :: (Monoid k, Foldable f) => f (Sort3 i j k a a) -> Sort3 i j k a a
```

### S5.8 — Fmt-inspired combinators

```haskell
-- | Sort by a key extractor (named after fmt1).
sort1 :: (a -> k) -> Sort3 i Int k a a

-- | Sort an Either: apply left sort to Lefts, right sort to Rights.
either3 :: Sort3 i j k a c -> Sort3 i j k b c -> Sort3 i j k (Either a b) c

-- | Sort a Maybe: apply sort to Justs, use default for Nothings.
maybe3 :: c -> Sort3 i j k a c -> Sort3 i j k (Maybe a) c
```

## Hedgehog properties

| Prop  | Description                                                      |
|-------|------------------------------------------------------------------|
| P51   | `sortingBytes` preserves all bytes (sum of group lengths = input length) |
| P52   | `sortingBytes` groups share same key                             |
| P53   | `groupingBytes` keys = set of byte values in input               |
| P54   | `sortingChars` preserves all chars                               |
| P55   | Rxlens on Sort3 typechecks and produces consistent results       |
| P56   | Rxprism on Sort3 (Monoid i) typechecks and produces results      |
| P57   | Indexed+coindexed chain produces correct grouping                |
| P58   | Category: `id . f = f` and `f . id = f` for Sort3               |
| P59   | Category: `(f . g) . h = f . (g . h)` for Sort3                 |
| P60   | `either3 l r` agrees with partition + separate sorts             |

## Work order

1. S5.6 — Evaluate sequences redesign (read-only, produces design doc)
2. S5.1 — sortingBytes, groupingBytes + P51–P53
3. S5.2 — sortingChars + P54
4. S5.3 — Rxlens + Sort3 test (P55)
5. S5.4 — Rxprism + Sort3 test (P56)
6. S5.5 — Indexed+coindexed chain test (P57)
7. S5.7 — Category, bind, cat for Sort3 (P58–P59)
8. S5.8 — sort1, either3, maybe3 combinators (P60)

## Key files

- `profunctor-optics-sort/src/Data/Profunctor/Optic/Sort.hs` — new operators
- `profunctor-optics-sort/test/Test/Prop/Sort.hs` — new properties
- `profunctor-optics-strings/src/Data/ByteString/Optic.hs` — reference
- `profunctor-optics-strings/src/Data/Text/Optic.hs` — reference
- `profunctor-optics-sort/src/Data/Profunctor/Optic/Import.hs` — Rxlens, Rxprism
- `/Users/cmk/Documents/Code/haskell/stringfmt/src/Data/Fmt/Type.hs` — Fmt reference

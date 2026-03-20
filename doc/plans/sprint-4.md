# Sprint 4 — Sort3 carriers for representable types

## Scope

Design and implement concrete Sort3 carriers (`mkSort3`) for
`Fin n`-indexed types, compose them with the cotraversal and grate
optics from `profunctor-optics-strings`, and write operators that
exploit Sort3's Closed + Corepresentable instances.

## Rationale

Sort3's input `(i -> (k, a))` is a representable container of
keyed values — the same shape as `Word8 ≅ (I8 -> Bool)` from the
strings package. A Sort3 carrier for finite index types gives
radix-sort steps over Word types, composable with `grate8`/`bits8`/
`ibits8` via `sortingUnder` (Colens) and cotraversal composition
(Cotraversing when Monoid i).

## Stories

| ID    | Module / target               | Description                                           |
|-------|-------------------------------|-------------------------------------------------------|
| S4.1  | Data.Profunctor.Sort          | `mkSort3` for `Fin n`-indexed types (Bounded, Enum)   |
| S4.2  | Data.Profunctor.Optic.Sort    | Cotraversal operator: compose `bits8` with Sort3      |
| S4.3  | Data.Profunctor.Optic.Sort    | Colens operator: compose `grate8` with Sort3          |
| S4.4  | Data.Profunctor.Optic.Sort    | Cxlens operator: compose `ibits8` with Sort3          |
| S4.5  | Data.Profunctor.Optic.Sort    | `zipsSorting`: merge Sort3 results via `zipsWith`     |
| S4.6  | Test.Prop.Sort                | Hedgehog properties for Sort3 operators               |

## New functions

### S4.1 — mkSort3

```haskell
-- | Identity Sort3 carrier for finite index types.
-- Groups input positions by key, producing a lookup by group and key.
mkSort3 :: (Bounded i, Enum i, Ord k) => Sort3 i Int k a a

-- | Re-key a Sort3 carrier by a projection (analogous to sortOn1).
sortOn3 :: (k' -> k) -> Sort3 i j k a b -> Sort3 i j k' a b
```

### S4.2 — Cotraversal composition

```haskell
-- | Sort through a cotraversal. Uses Sort3 as carrier, requiring
-- Monoid i for Cotraversing. The cotraversal lifts Sort3 through
-- a Distributive functor.
cosortingOf :: (Monoid i, Ord k)
            => Cotraversal s t a b -> Sort3 i j k a b -> Sort3 i j k s t
```

### S4.3 — Colens composition (already exists as sortingUnder)

```haskell
-- sortingUnder :: Colens s t a b -> Sort3 i j k a b -> Sort3 i j k s t
-- Already implemented. Verify it composes with grate8/grate16/etc.
```

### S4.4 — Cxlens (indexed cotraversal) composition

```haskell
-- | Sort through an indexed cotraversal. The coindex flows through
-- as group metadata.
cosortingCx :: (Monoid i, Monoid r, Ord k)
            => Cxlens r s t a b -> Sort3 i j k a b -> Sort3 i j k s t
```

### S4.5 — Merge via zipsWith

```haskell
-- | Merge two Sort3 results pointwise through a grate.
zipsSorting :: AColens s t a b -> (a -> a -> b) -> Sort3 i j k s t -> Sort3 i j k s t -> Sort3 i j k s t
```

## Hedgehog properties (S4.6)

| Prop  | Description                                                      |
|-------|------------------------------------------------------------------|
| P25   | `mkSort3`: identity law — `runSort3 mkSort3 inp j k = snd (inp (encode j k))` for the chosen encoding |
| P26   | `mkSort3`: all positions accounted for — every `i` appears in some group |
| P27   | `sortingUnder grate8`: roundtrip with `over grate8 id` is identity |
| P28   | `cosortingOf bits8`: groups Bool values correctly                |
| P29   | `sortOn3 f . mkSort3` agrees with `mkSort3` on re-keyed input   |
| P30   | `zipsSorting`: `zipsWith grate8 (&&) 0xFF 0xAA` = `0xAA`        |

## Work order

1. S4.1 — Design and implement `mkSort3`, `sortOn3`
2. S4.6 — Write P25–P26 skeletons
3. S4.3 — Verify `sortingUnder` with `grate8` (P27)
4. S4.2 — Implement `cosortingOf` (P28)
5. S4.4 — Implement `cosortingCx`
6. S4.5 — Implement `zipsSorting` (P30)
7. Green P25–P30

## Dependencies

May require adding `scheme-extensions` (for `I8`/`IN` types) and
`profunctor-optics-strings` (for `grate8`/`bits8`/`ibits8`) to
`profunctor-optics-sort`'s build-depends, or creating the Sort3
carriers generically enough that they work with any
`Bounded`/`Enum` index type.

## Key files

- `profunctor-optics-sort/src/Data/Profunctor/Sort.hs` — mkSort3, sortOn3
- `profunctor-optics-sort/src/Data/Profunctor/Optic/Sort.hs` — new operators
- `profunctor-optics-strings/src/Data/Word/Optic.hs` — grate8, bits8, ibits8 (reference)
- `profunctor-optics/src/Data/Profunctor/Optic/Lens.hs` — zipsWith (reference)

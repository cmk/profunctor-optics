# profunctor-optics-sort

Profunctor-based sorting and grouping optics.

## Overview

Three Sort profunctors exploring the design space of discrimination
as a profunctor operation:

| Variant | Shape | Instances |
|---|---|---|
| `Sort1 k a b` | `NonEmpty (k, a) -> [NonEmpty b]` | Profunctor, Strong, Choice |
| `Sort2 k a b` | `NonEmpty (k, a) -> NonEmpty [b]` | Profunctor, Strong, Choice, Costrong, Cochoice |
| `Sort3 i j k a b` | `(i -> (k, a)) -> j -> k -> b` | Profunctor, Closed, Costrong, Cosieve, Corepresentable |

Sort1 and Sort3 are complementary halves: Sort1 gets Strong + Choice
(concrete elements, can fail), Sort3 gets Closed (representable,
total). Sort2 sits between. The failure/totality axis IS the
Strong-vs-Closed axis.

## Sort3 and representable containers

Sort3's input is `(i -> (k, a))` — a representable container of
keyed values. This is the same shape as the bit-level representations
in `profunctor-optics-strings`, where `Word8 ≅ (I8 -> Bool)`.

### Sort3 as a radix sort step

If `i = I8`, `k = Bool` (bit value as key), `a = Bool`, then
`Sort3 I8 j Bool Bool Bool` is: "given a tabulation of 8 keyed bits,
produce a result indexed by group and key." That's a single radix
sort pass — partition bits into `False`-bucket and `True`-bucket.

### Colens composition

`grate8 :: Colens Word8 Word8 (I8 -> Bool) (I8 -> Bool)` can lift
a Sort3 through `sortingUnder grate8`, sorting at the
bit-representation level. The `zipsWith` operation on grates means
you can also combine/merge sort results pointwise across two Word8s.

### Cotraversal composition (Monoid i)

`bits8 :: Cotraversal Word8 Word8 Bool Bool` can compose with Sort3
when `i` is a Monoid, since Sort3 then satisfies `Cotraversing`.
This lets you sort/group at the individual-bit level through the
cotraversal.

### Indexed cotraversal (Cxlens)

`ibits8` gives position-aware access — the index IS the bit
position. This maps directly onto Sort3's coindexed optic carrier
shape:

```
Cxtraversal k s t a b ≅ (f a -> k -> b) -> f s -> t
Sort3 i j k a b       ≅ (i -> (k, a)) -> j -> k -> b
```

So `ibits8` can thread bit positions through Sort3 as coindices.

### Sort3Corep and Coapplicative

`Sort3Corep i j k` is the corepresentation of Sort3. It bundles
a tabulated input `(i -> (k, a))` with a group position `j` and
key `k`. Unconditionally `Functor`. With `Monoid i`, also `Coapply`
and `Coapplicative` (sampling at `mempty`, mirroring the `(->) r`
instance from the `coapplicative` package). This makes Sort3
satisfy `Cotraversing` when `i` is a Monoid.

## Modules

| Module | Contents |
|---|---|
| `Data.Profunctor.Sort` | Sort1, Sort2, Sort3 types + instances, Sort3Corep |
| `Data.Profunctor.Optic.Sort` | Operators: sorting, grouping, nubbing, container construction, joins |
| `Data.Profunctor.Optic.Import` | Re-exports from profunctor-optics + dual optic types (Relens, Reprism) |

## Dependencies

```
base, coapplicative, containers, profunctors, profunctor-optics
```

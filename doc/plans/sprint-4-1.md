# Sprint 4-1 — SortF: the indexed Fmt

## Scope

Introduce `SortF i k a b = (i -> (k, a)) -> b` as the simplified
Sort3 (dropping `j`), port the Fmt API over, derive all instances
via `Costar`, and write SortF variants of existing operators.

## Rationale

Sort3's `j` parameter was prematurely committing to an output
structure (`j -> k -> b`). Dropping it gives `SortF i k a b`,
which is `Costar (Compose ((->) i) ((,) k))` — the indexed
profunctor generalization of `Fmt m a b = (m -> a) -> b`.

```
Fmt   m a b = SortF m () a b    -- indexed by m, trivial key
SortF i k a b                    -- indexed by i, keyed by k
```

All instances derive via `Costar`. Category and Arrow come for
free when `Monoid i`. The Fmt combinator vocabulary (`(%)`, `bind`,
`cat`, `fmt1`, `either1`, `maybe1`) translates directly.

## Stories

| ID     | Module / target               | Description                                        |
|--------|-------------------------------|----------------------------------------------------|
| S4-1.1 | Data.Profunctor.Sort          | Define SortF, SortFCorep, DerivingVia instances    |
| S4-1.2 | Data.Profunctor.Sort          | Port Fmt API: (%), bind, cat, sortF, sortF1        |
| S4-1.3 | Data.Profunctor.Sort          | mkSortF, mkSortFN carriers                         |
| S4-1.4 | Data.Profunctor.Optic.Sort    | SortF variants of existing operators               |
| S4-1.5 | Data.Profunctor.Optic.Sort    | SortF merge tactics (sortedMatchedF, sortedMissingF) |
| S4-1.6 | Test.Prop.Sort                | Hedgehog properties for SortF                      |

## New types

### S4-1.1 — SortF type and instances

```haskell
newtype SortF i k a b = SortF { runSortF :: (i -> (k, a)) -> b }
  deriving (Functor, Applicative, Monad)
    via Costar (Compose ((->) i) ((,) k)) a
  deriving (Profunctor, Closed, Costrong, Cochoice)
    via Costar (Compose ((->) i) ((,) k))

-- Cosieve / Corepresentable (may need hand-rolling if Compose
-- blocks representational equality for the fundep)
type SortFCorep i k a = Compose ((->) i) ((,) k) a  -- = i -> (k, a)

-- Category / Arrow when Monoid i
deriving via Costar (Compose ((->) i) ((,) k))
  instance Monoid i => Category (SortF i k)

deriving via Costar (Compose ((->) i) ((,) k))
  instance Monoid i => Arrow (SortF i k)

-- Choice when Monoid i (via Coapplicative on Corep)
deriving via Costar (Compose ((->) i) ((,) k))
  instance Monoid i => Choice (SortF i k)

-- Strong when Monoid i (via Arrow)
deriving via Costar (Compose ((->) i) ((,) k))
  instance Monoid i => Strong (SortF i k)
```

### Relationship to Sort3

```haskell
-- Sort3 is recoverable:
type Sort3 i j k a b = SortF i k a (j -> k -> b)

-- Or more precisely, Sort3 was SortF with a fixed output shape.
-- SortF subsumes Sort3 by letting b be free.
```

## New functions

### S4-1.2 — Fmt API port

```haskell
-- | Run a SortF.
runSortF :: SortF i k a b -> (i -> (k, a)) -> b

-- | Constant: this key, this value.
sortF :: k -> a -> SortF i k a (k, a)

-- | Unary: sort by key extractor (= fmt1).
sortF1 :: (a -> (k, b)) -> SortF i k b (a -> ?)
-- More precisely:
-- type SortF1 i k s a = SortF i k s (a -> s)

-- | Compose two sort passes (= Fmt's (%)).
-- Keys accumulate via Semigroup.
(%) :: Semigroup k => SortF i k b c -> SortF i k a b -> SortF i k a c
-- This IS Category (.) — just re-exported with the Fmt name.

-- | Key-dependent refinement (= Fmt's bind).
bindSortF :: SortF i k a b -> ((k, a) -> SortF i k a' a) -> SortF i k a' b

-- | Fold multiple sort passes (= Fmt's cat).
catSortF :: (Monoid k, Foldable f) => f (SortF i k a a) -> SortF i k a a

-- | Remap keys (= Fmt's refmt = our sortOn3).
remapSortF :: (k1 -> k2) -> SortF i k1 a b -> SortF i k2 a b

-- | Sum-type combinators (= Fmt's either1/maybe1).
eitherSortF :: SortF i k a c -> SortF i k b c -> SortF i k (Either a b) c
maybeSortF :: c -> SortF i k a c -> SortF i k (Maybe a) c
```

### S4-1.3 — Carriers

```haskell
-- | Identity carrier for finite index types.
mkSortF :: (Bounded i, Enum i, Ord k) => SortF i k a (Map k [a])

-- | Identity carrier for Int-indexed containers.
mkSortFN :: Ord k => Int -> SortF Int k a (Map k [a])

-- | Identity carrier grouping into NonEmpty.
mkSortFNE :: (Bounded i, Enum i, Ord k) => SortF i k a (Map k (NonEmpty a))
```

### S4-1.4 — SortF variants of existing operators

Port each existing operator, noting simplifications:

```haskell
-- sortingUnder already works (Closed)
sortingUnderF :: Colens s t a b -> SortF i k a b -> SortF i k s t

-- cosortingOf already works (Cotraversing, Monoid i)
cosortingOfF :: Monoid i => Cotraversal s t a b -> SortF i k a b -> SortF i k s t

-- zipsSorting: same shape, b is free
zipsSortingF :: (b -> b -> b) -> SortF i k a b -> SortF i k a b -> SortF i k a b

-- sortingVector: output type is now in b directly
sortingVectorF :: Ord k => (a -> k) -> V.Vector a -> Map k (V.Vector a)
-- Uses mkSortFN, materializes into Map k (V.Vector a)

-- Merge tactics: i=() since one position per key
sortedMatchedF :: SortF () k (x, y) z -> Merge.SimpleWhenMatched k x y z
sortedMissingF :: SortF () k x y -> Merge.SimpleWhenMissing k x y

-- Container construction
toMapOfF :: Ord a => Lens' s a -> NonEmpty s -> Map a (NonEmpty s)
-- Same implementation, uses SortF internally

-- mergingOf: same pipeline, SortF under the hood
mergingOfF :: Ord a => Lens' s a -> Lens' t a -> ... -> Map a c
```

### S4-1.5 — New operators enabled by Category

```haskell
-- | Two-pass sort: sort by k1, then refine by k2.
-- Uses Category composition.
sortFBy :: (Ord k1, Ord k2, Bounded i, Enum i)
        => (a -> k1) -> (a -> k2)
        -> SortF i (k1, k2) a (Map (k1, k2) [a])

-- | Multi-key sort via cat.
sortFByAll :: (Ord k, Bounded i, Enum i, Foldable f)
           => f (a -> k) -> SortF i [k] a (Map [k] [a])
```

## Hedgehog properties

| Prop  | Description                                                      |
|-------|------------------------------------------------------------------|
| P4-1  | DerivingVia: `dimap id id = id` for SortF                       |
| P4-2  | Category: `id . f = f` for SortF                                |
| P4-3  | Category: `f . id = f` for SortF                                |
| P4-4  | Category: `(f . g) . h = f . (g . h)` for SortF                |
| P4-5  | `mkSortF` groups by key correctly                               |
| P4-6  | `mkSortFN` preserves element count                              |
| P4-7  | `sortingUnderF grate8` composes correctly                        |
| P4-8  | `cosortingOfF bits8` composes correctly (Monoid i)               |
| P4-9  | `sortedMatchedF` plugs into Map.merge correctly                  |
| P4-10 | `eitherSortF` partitions correctly                               |
| P4-11 | `maybeSortF` handles Nothing with default                        |
| P4-12 | `catSortF` folds multiple passes                                 |
| P4-13 | `bindSortF` allows key-dependent refinement                      |
| P4-14 | `remapSortF id = id`                                             |

## Work order (TDD)

1. S4-1.1 — SortF type + DerivingVia instances
2. S4-1.6 — P4-1 skeleton (test DerivingVia works)
3. S4-1.3 — mkSortF, mkSortFN carriers + P4-5, P4-6
4. S4-1.2 — Fmt API port: (%), bind, cat, sortF1, eitherSortF, maybeSortF + P4-2..P4-4, P4-10..P4-14
5. S4-1.4 — Port existing operators to SortF + P4-7..P4-9
6. S4-1.5 — Merge tactics
7. Green all properties

## Key files

- `profunctor-optics-sort/src/Data/Profunctor/Sort.hs` — SortF type, carriers, Fmt API
- `profunctor-optics-sort/src/Data/Profunctor/Optic/Sort.hs` — SortF operators
- `profunctor-optics-sort/test/Test/Prop/Sort.hs` — new properties
- `/Users/cmk/Documents/Code/haskell/stringfmt/src/Data/Fmt/Type.hs` — Fmt reference

## Migration note

Sort3 remains as-is for now. SortF is added alongside it.
Once SortF is validated, Sort3 can be defined as a type alias:

```haskell
type Sort3 i j k a b = SortF i k a (j -> k -> b)
```

Or Sort3 may be retired entirely if SortF + free `b` proves
strictly better in practice.

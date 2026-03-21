# Sprint Sort — Profunctor sort operators

## Scope

Systematically explore the operator design space for Sort1, Sort2,
and Sort3: for each Sort variant, for each profunctor instance it
has, write the natural operators that compose optics with Sort
carriers. Refactor poorly-designed existing operators. Add Hedgehog
property tests for profunctor laws and optic-level behavior.

## Rationale

Sort1/Sort2/Sort3 have hand-rolled profunctor instances but sparse
operators. The existing `sortingOf` shows the pattern works — an
optic transforms a Sort carrier, then `runSort` unwraps. The rest
of the discrimination API (nub, group, toMap, toSet, joins) and the
full instance set (Strong, Choice, Closed, Costrong, Cochoice,
Cosieve, Corepresentable) are unexploited.

## Stories

| ID    | Module / target               | Description                                              |
|-------|-------------------------------|----------------------------------------------------------|
| SS.1  | Data.Profunctor.Optic.Sort    | Refactor: push joins to bottom, replace min/max folds    |
| SS.2  | Data.Profunctor.Optic.Sort    | Sort1 Lens operators: `sortingDescOf`, container ops     |
| SS.3  | Data.Profunctor.Optic.Sort    | Sort2 operators: `nubbingBack`, `groupingDescBack`       |
| SS.4  | Data.Profunctor.Optic.Sort    | Sort3 scaffolding: `ASort3`, `builds3`                   |
| SS.5  | Data.Profunctor.Optic.Sort    | Indexed operators: `toMapIx`                             |
| SS.6  | Data.Profunctor.Sort          | Sort3 carrier: explore `mkSort3` design                  |
| SS.7  | Test.Prop.Sort                | Hedgehog property tests                                  |

## Refactoring (SS.1)

Push to bottom of module (not optic operators, keep as-is):
- `joiningOf`, `innerJoinOf`, `outerJoinOf`, `leftJoinOf`, `rightJoinOf`
- `combineGroup`, `partitionEithers`

Replace `minimumSorting` / `maximumSorting` with general per-group fold:
```haskell
foldSorting1 :: Ord a => Lens' s a -> (s -> s -> s) -> NonEmpty s -> [s]
foldSorting1 o f = map (foldr1 f) . sortingOf o
```

Keep `foldSorting` and `mconcatSorting` as-is (well-designed).

## New functions

### SS.2 — Sort1 Lens operators (Strong + Choice)

```haskell
-- Descending sort through a lens
sortingDescOf :: Ord a => Lens' s a -> NonEmpty s -> [NonEmpty s]

-- Map keyed by lens focus, values are groups
toMapOf :: Ord a => Lens' s a -> NonEmpty s -> Map a (NonEmpty s)

-- Map with explicit per-element value transform and semigroup combine
toMapWithOf :: (Ord a, Semigroup v)
            => Lens' s a -> (s -> v) -> NonEmpty s -> Map a v

-- Count occurrences per key
countingOf :: Ord a => Lens' s a -> NonEmpty s -> Map a Int
```

### SS.3 — Sort2 operators (+ Costrong + Cochoice)

```haskell
-- Deduplicate via Sort2 (head of each group, >=1 group guaranteed)
nubbingBack :: Ord a => Lens' s a -> NonEmpty s -> NonEmpty (Maybe s)

-- Descending grouping via Sort2
groupingDescBack :: Ord a => Lens' s a -> NonEmpty s -> NonEmpty [s]
```

### SS.4 — Sort3 scaffolding (Closed + Costrong + Cosieve + Corepresentable)

```haskell
-- Reified Sort3 optic
type ASort3 i j k s t a b = Sort3 i j k a b -> Sort3 i j k s t

-- Core runner (uniform naming with builds1/builds2)
builds3 :: ASort3 i j k s t a b -> Sort3 i j k a b -> Sort3 i j k s t
```

### SS.5 — Indexed operators

```haskell
-- Indexed toMap: key = index from Ixlens
toMapIx :: Ord k => Ixlens' k s a -> NonEmpty (k, s) -> Map k (NonEmpty s)
```

### SS.6 — Sort3 carrier design (exploratory)

Design `mkSort3` for concrete `i`/`j`. Candidates:
- `i = Int` (input position), `j = Int` (group index)
- Requires experimentation. Gated on finding natural use cases.

## Hedgehog properties (SS.7)

### Profunctor laws (per Sort variant)

| Prop  | Sort | Description                                                        |
|-------|------|--------------------------------------------------------------------|
| P1    | 1    | `dimap id id = id`                                                 |
| P2    | 1    | `dimap (g . f) (h . k) = dimap f k . dimap g h`                   |
| P3    | 1    | `first' . dimap f g = dimap (first f) (first g) . first'`         |
| P4    | 1    | `left' . dimap f g = dimap (left f) (left g) . left'`             |
| P5    | 2    | `dimap id id = id`                                                 |
| P6    | 2    | `unfirst . first' = id` (Costrong/Strong roundtrip)                |
| P7    | 2    | `unleft . left' = id` (Cochoice/Choice roundtrip)                  |
| P8    | 3    | `dimap id id = id`                                                 |
| P9    | 3    | `closed` distributes: `closed . closed = dimap flip flip . closed` |
| P10   | 3    | `cosieve (cotabulate f) = f` (Corepresentable roundtrip)           |
| P11   | 3    | `cotabulate (cosieve p) = p` (Corepresentable roundtrip)           |

### Operator-level properties

| Prop  | Description                                                          |
|-------|----------------------------------------------------------------------|
| P12   | `sortingOf o` groups share same key: `all (\g -> allEqual (fmap (view o) g))` |
| P13   | `sortingOf o` groups are in ascending key order                      |
| P14   | `sortingOf o` preserves all elements (concat groups = sort of input) |
| P15   | `nubbingOf o` returns one element per distinct key                   |
| P16   | `sortingDescOf o` groups are in descending key order                 |
| P17   | `toMapOf o` keys = set of focused values                             |
| P18   | `toMapOf o` values agree with `sortingOf o` groups                   |
| P19   | `groupingBack o` produces ≥1 group (NonEmpty outer)                  |
| P20   | `groupingBack o` total element count = input count                   |
| P21   | `foldSorting1 o const` agrees with `nubbingOf o` (first per group)  |

### Sort3Corep properties (Monoid i => Coapplicative)

| Prop  | Description                                            |
|-------|--------------------------------------------------------|
| P22   | `coapply . fmap Left = Left`                           |
| P23   | `coapply . fmap Right = Right`                         |
| P24   | `copure . fmap f = f . copure`                         |

## Work order (TDD)

1. SS.7 — Write P1–P24 skeletons (all red)
2. SS.1 — Refactor: push joins, replace min/max. Green P12–P15, P21
3. SS.2 — Sort1 operators: `sortingDescOf`, `toMapOf`, `toMapWithOf`, `countingOf`. Green P16–P18
4. SS.3 — Sort2 operators: `nubbingBack`, `groupingDescBack`. Green P19–P20
5. SS.4 — Sort3 scaffolding: `ASort3`, `builds3`
6. SS.5 — Indexed: `toMapIx`
7. Verify P1–P11 profunctor laws, P22–P24 Coapplicative laws
8. Commit when P1–P24 all pass

## Stretch goals

- Sort1 Prism operator: `partitioningOf` (uses Choice instance)
- Sort2 Relens/Reprism operators (uses Costrong/Cochoice)
- Sort3 `mkSort3` and Cotraversal operators (uses Corepresentable)
- Coindexed `sortingCx` for Sort3

## Key files

- `profunctor-optics-sort/src/Data/Profunctor/Optic/Sort.hs` — operators (primary)
- `profunctor-optics-sort/src/Data/Profunctor/Sort.hs` — carrier types
- `profunctor-optics-sort/profunctor-optics-sort.cabal` — deps
- `profunctor-optics/src/Data/Profunctor/Optic/Property.hs` — optic-level predicates (reference)
- `profunctor-optics-folds/src/Data/Profunctor/Optic/Machine.hs` — buildl pattern (reference)

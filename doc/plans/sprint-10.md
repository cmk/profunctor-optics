# Sprint 10 — Locate proper modules for Sort operators

## Scope

Place each upstream-safe Sort operator in its natural module within
profunctor-optics, following the existing organization: Lens.hs for
lenses and colenses (+ indexed), Traversal.hs for traversals and
cotraversals, Fold.hs for folds and cofolds, Setter.hs for setters
and resetters, View.hs for views and reviews.

## Rationale

The existing modules are organized by optic type:
- **Lens.hs**: Lens, Colens, Ixlens, Cxlens, zipsWith, coview
- **Traversal.hs**: Traversal, Cotraversal, traverses, cotraverses
- **Fold.hs**: Fold, Cofold, folds, cofolds, lists
- **Setter.hs**: Setter, Resetter, set, sets, reset, resets
- **View.hs**: View, Review, view, review
- **Combinator.hs**: (.), (%), (#), reps, coreps, etc.
- **Carrier.hs**: carrier types and with* extractors

Sort operators should follow the same pattern based on what optic
type they consume.

## Module placement

### Carrier.hs — Sort type

```haskell
-- Sort type, instances, runSort
-- Category, Choice instances
-- No operators — just the carrier definition
```

### Combinator.hs — Sort composition operators

```haskell
-- (%.) — Sort-specific composition (already uses (.) for Category)
-- bindSort — key-dependent refinement
-- catSort — fold sort passes
-- eitherSort, maybeSort — sum-type combinators
-- zipsSorting — pointwise merge of Sort carriers
-- sortF, remapSort — construction
```

These are profunctor combinators, not optic operators. They go
alongside `(%)`, `(#)`, `reps`, `coreps`.

### Lens.hs — Lens/Colens-based sort operators

The existing Operators section has `zipsWith`, `coview`, `toPastro`,
`toTambara`, etc. Sort-through-a-lens operators fit here:

```haskell
-- Lens-based (Strong):
sortingOfL :: Ord a => Lens' s a -> [s] -> [[s]]
groupingOfL :: Ord a => Lens' s a -> [s] -> [[s]]
nubbingOfL :: Ord a => Lens' s a -> [s] -> [s]

-- Colens-based (Closed):
-- Colens optics compose with Sort by direct application — no
-- operator needed. Document this alongside zipsWith.
```

### Fold.hs — Post-sort fold operators

```haskell
-- These consume sortingOf results with folds:
foldSortingL :: Ord a => Lens' s a -> (s -> r -> r) -> r -> [s] -> [r]
foldSorting1L :: Ord a => Lens' s a -> (s -> s -> s) -> [s] -> [s]
mconcatSortingL :: (Ord a, Monoid m) => Lens' s a -> (s -> m) -> [s] -> [m]
```

### View.hs / Setter.hs — not applicable

Sort operators produce groups, not single values. They don't
naturally fit in View (which extracts one value) or Setter (which
modifies in place).

### New: Optic/Sort.hs in profunctor-optics core?

Alternatively, if the module set is getting crowded, create a new
`Data.Profunctor.Optic.Sort` in profunctor-optics itself for all
Sort-related operators that only need core deps:

```haskell
module Data.Profunctor.Optic.Sort
  ( -- re-export Sort from Carrier
    Sort(..), runSort
    -- composition
  , (%.), bindSort, catSort
  , sortF, remapSort
  , eitherSort, maybeSort, zipsSorting
    -- carriers
  , mkSort, mkSortN
    -- Lens-based operators
  , sortingOfL, groupingOfL, nubbingOfL
  , sortingDescOfL
  , toMapOfL, countingOfL
    -- generic representable
  , sortingRep, sortUniqueRep, sortTaggedRep, groupTaggedRep
    -- merge
  , mergingOfL, innerMergeL, outerMergeL, leftMergeL, rightMergeL
  , sortedMatched, sortedMissing
    -- post-sort folds
  , foldSortingL, foldSorting1L, mconcatSortingL
  )
```

This avoids polluting Lens.hs/Fold.hs with sort-specific
functions and keeps the sort API discoverable in one place.

## Coindexed operators — the gap

### What's missing

The existing sort operators are all on the **indexed** (Strong)
side:
- `sortingOfL` uses `Lens'` (Strong)
- `sortingIx` uses `Ixlens'` (indexed Strong)

The **coindexed** (Closed) side has no operators:
- No `Cxlens`-based sort operators
- No `(#)` composition through Sort carriers
- No `reoverWithKey`/`corepsWithKey` usage
- `ibits8` composes with Sort (proven in benchmarks) but there's
  no named operator for it

### What should exist

```haskell
-- Coindexed sort: the dual of sortingIx.
-- Uses Cxlens (Closed, coindexed) instead of Ixlens (Strong, indexed).
-- The coindex flows through the Sort's Closed instance.
sortingCx :: (Monoid k, Ord k')
          => Cxlens' k s a -> Sort I k' a (Map k' [a]) -> Sort I k' s (Map k' [s])
-- or: the Cxlens IS the optic, just apply it to the carrier.
-- This might be another trivial identity like sortingUnderF was.

-- Coindexed fold: extract coindexed results
cofoldsSortWithKey :: Monoid k => Cxoptic' (Sort i) k s a -> (k -> a -> r) -> s -> r

-- Coindexed traversal composition with Sort:
-- (#) :: Cxoptic ... -> Cxoptic ... -> Cxoptic ...
-- Compose two coindexed optics through Sort, keys accumulate.
```

### The honest assessment

Most coindexed operators may be trivial identities (the optic IS
function application on Sort, since Sort has Closed). The useful
coindexed operations are:
1. **`reoverWithKey`** — apply a key-dependent function through
   a coindexed optic on a Sort carrier
2. **`corepsWithKey`** — extract the coindexed corepresentation
3. **`(#)` composition** — compose coindexed optics with monoidally
   accumulated keys, using Sort as the carrier

These need to be tested to see which produce non-trivial operators.

## Stories

| ID     | Module / target                | Description                                    |
|--------|--------------------------------|------------------------------------------------|
| S10.1  | profunctor-optics              | Create Optic/Sort.hs or place in existing mods |
| S10.2  | profunctor-optics              | Move upstream-safe operators                   |
| S10.3  | profunctor-optics              | Add coindexed Sort operators                   |
| S10.4  | profunctor-optics              | Add (#)-based coindexed composition tests      |
| S10.5  | profunctor-optics              | Add reoverWithKey/corepsWithKey Sort operators  |
| S10.6  | Tests                          | Full property suite for upstream operators      |

## Key files

- `profunctor-optics/src/Data/Profunctor/Optic/Carrier.hs`
- `profunctor-optics/src/Data/Profunctor/Optic/Lens.hs`
- `profunctor-optics/src/Data/Profunctor/Optic/Combinator.hs`
- `profunctor-optics/src/Data/Profunctor/Optic/Fold.hs`

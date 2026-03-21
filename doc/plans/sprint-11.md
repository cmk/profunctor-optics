# Sprint 11 — Coindexed Sort operators

## Scope

Fill the coindexed gap: add operators that use Sort with `Cxlens`,
`Cxtraversal`, `(#)` composition, `reoverWithKey`, and
`corepsWithKey`. Test which produce non-trivial operators and
which are trivial identities.

## Rationale

The indexed (Strong) side is well-covered: `sortingOf` (Lens),
`sortingIx` (Ixlens), `(%)` composition. The coindexed (Closed)
side has proven compositions (ibits8 + Sort, grate8 + Sort) but
no named operators or composition patterns.

The coindexed path matters because:
1. It's 88x faster than the cotraversal path (ibits8 vs bits8)
2. It threads position information as coindices
3. It composes with `(#)` for monoidally-accumulated coindices
4. It's the natural dual of the indexed operators

## Stories

| ID     | Module / target               | Description                                    |
|--------|-------------------------------|------------------------------------------------|
| S11.1  | Explore                       | Test which coindexed operators are non-trivial  |
| S11.2  | Optic/Sort.hs or Combinator   | Add reoverWithKey-based Sort operator           |
| S11.3  | Optic/Sort.hs or Combinator   | Add corepsWithKey-based Sort operator           |
| S11.4  | Optic/Sort.hs or Combinator   | Add (#)-based coindexed Sort composition        |
| S11.5  | Optic/Sort.hs                 | Cxlens-based sort operators (if non-trivial)    |
| S11.6  | Optic/Sort.hs                 | Costrong/Cochoice carrier transformers via `re`  |
| S11.7  | Tests + benchmarks            | Properties and perf for co-optic operators      |

## S11.1 — Triage: trivial vs non-trivial

### Trivial (optic = function application on Sort)

Since Sort has Closed, any Colens/Cxlens applied to a Sort carrier
is just function application:

```haskell
grate8 carrier  -- :: Sort I8 k Word8 Word8, just applies grate8
ibits8 carrier  -- :: Sort I8 k Word8 (I8 -> Word8), just applies ibits8
```

These don't need wrapper operators. Document in README.

### Potentially non-trivial

```haskell
-- 1. reoverWithKey through a Cxlens on Sort
-- reoverWithKey :: Monoid i => Cxoptic (->) i s t a b -> (i -> a -> b) -> s -> t
-- Applied to Sort: takes a coindexed optic and a key-dependent
-- function, produces a modified Sort.
-- This IS non-trivial if the Sort is being used as the profunctor
-- variable, not (->) .

-- 2. corepsWithKey extraction
-- corepsWithKey :: Corepresentable p => Monoid i
--              => Cxoptic p i s t a b -> (i -> Corep p a -> b) -> Corep p s -> t
-- Extracts the coindexed corepresentation of an optic over Sort.

-- 3. (#) composition of two coindexed optics over Sort
-- f # g :: Cxoptic (Sort i k) kx c1 c2 a1 a2
-- This accumulates coindices monoidally, running both optics
-- through the Sort carrier.
```

## S11.2 — reoverWithKey on Sort

```haskell
-- | Apply a coindex-dependent function through a Sort carrier.
--
-- The coindex @j@ (e.g. bit position from ibits8) is available
-- to the modification function.
--
-- @
-- cosortWithKey ibits8 (\\pos val -> ...) carrier
-- @
--
cosortWithKey :: Monoid j
              => Cxoptic' (Sort i k) j s a
              -> (j -> a -> a)
              -> Sort i k s s
```

## S11.3 — corepsWithKey on Sort

```haskell
-- | Extract the coindexed corepresentation of an optic over Sort.
--
-- Gives access to the Sort's Corep functor (Compose ((->) i) ((,) k))
-- alongside the coindex.
--
cosortRepsWithKey :: (Corepresentable (Sort i k), Monoid j)
                 => Cxoptic (Sort i k) j s t a b
                 -> (j -> Corep (Sort i k) a -> b)
                 -> Corep (Sort i k) s -> t
```

## S11.4 — (#) composition

```haskell
-- | Compose two coindexed optics through Sort.
-- Coindices accumulate monoidally.
--
-- @
-- ibits8 '#' ibits8 :: Cxoptic (Sort I8 k) I8 Word8 Word8 Bool Bool
-- @
--
-- (Uses (#) from Combinator.hs, just verify it works with Sort)
```

## Key question

How many of S11.2–S11.4 are actually useful for sorting/grouping,
vs being theoretically sound but practically useless? S11.1 triages
this. The benchmark showing ibits8 at 12ns (vs bits8 at 1072ns)
strongly suggests the coindexed path is the *practical* path for
Sort composition, so these operators have real value.

## S11.5–S11.6 — Costrong/Cochoice as carrier transformers via `re`

### The insight

A Lens lifts a Sort carrier (adds structure via Strong). `re`
reverses it: `re lens` collapses a Sort carrier (removes structure
via Costrong). Same for Prism/Choice → `re prism`/Cochoice.

These are **carrier transformers**: they reshape what a Sort
operates on without changing the discrimination logic.

### Operators

```haskell
-- | Collapse a product-Sort to a component-Sort.
-- Takes a Lens (which lifts), reverses it with re to collapse.
--
-- @
-- collapseProduct fstL :: Sort2 k (a, c) (a, c) -> Sort2 k a a
-- @
--
collapseProduct :: Costrong p => Lens s t a b -> p s t -> p a b
collapseProduct o = re o

-- | Filter a sum-Sort to one branch.
-- Takes a Prism (which branches), reverses it with re to filter.
--
-- @
-- filterBranch left' :: Sort2 k (Either a c) (Either a c) -> Sort2 k a a
-- @
--
filterBranch :: Cochoice p => Prism s t a b -> p s t -> p a b
filterBranch o = re o
```

Note: both are `re o` — they're named for documentation, not
implementation. The value is in making the pattern explicit:
"I have a Sort on pairs, I want a Sort on first-components,
so I collapse via `re fstL`."

### Composition chains

The interesting case: chain lift and collapse to reshape Sort
carriers through multiple levels:

```haskell
-- Lift to pairs, sort, collapse back:
-- re fstL . fstL = id (roundtrip)

-- Lift to Either, sort Lefts, collapse:
-- re left' . left' = id

-- Lift to pairs via fstL, then collapse to second component
-- via re sndL — this RESHAPES: extracts snd from a pair-sort:
-- re sndL . fstL :: Sort k a a -> Sort k (a, c) (a, c) -> Sort k c c
```

The general pattern: `re lens2 . lens1` reshapes from `lens1`'s
focus to `lens2`'s focus. This is a **sort-carrier reindexing**
operation.

### Properties for carrier transformers

| Prop  | Description                                                     |
|-------|-----------------------------------------------------------------|
| P84   | `re fstL . fstL` on Sort2 = id (roundtrip)                     |
| P85   | `re left' . left'` on Sort2 = id (roundtrip)                   |
| P86   | `re fstL` collapses pair-Sort to first-component-Sort           |
| P87   | `releft` filters Either-Sort to Left-branch-Sort                |
| P88   | Reshaping: `re sndL . fstL` extracts second from pair-sort      |

## Hedgehog properties

| Prop  | Description                                                     |
|-------|-----------------------------------------------------------------|
| P80   | `cosortWithKey ibits8 (\_ b -> b) carrier == carrier`           |
| P81   | `cosortWithKey ibits8 (\i _ -> f i) carrier` applies f          |
| P82   | `(#)` coindexed composition typechecks and runs on Sort         |
| P83   | Coindexed keys accumulate correctly through (#)                 |
| P84   | `re fstL . fstL` on Sort2 = id (roundtrip)                     |
| P85   | `re left' . left'` on Sort2 = id (roundtrip)                   |
| P86   | `re fstL` collapses pair-Sort to first-component-Sort           |
| P87   | `releft` filters Either-Sort to Left-branch-Sort                |
| P88   | Reshaping: `re sndL . fstL` reindexes a Sort carrier            |

## Key files

- `profunctor-optics/src/Data/Profunctor/Optic/Combinator.hs` — (#), reoverWithKey, corepsWithKey
- `profunctor-optics/src/Data/Profunctor/Optic/Carrier.hs` — Sort, Corep
- `profunctor-optics-sort/test/Test/Prop/Sort.hs` — new properties

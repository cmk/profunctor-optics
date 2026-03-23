# Sprint 18 — Dissolve Combinator.hs

## Scope

Break up `Data.Profunctor.Optic.Combinator` into its natural homes
and remove the module. Every export moves to exactly one of three
existing or new modules.

## Rationale

Combinator.hs is a kitchen sink: arrow-style combinators, divisible
combinators, index/coindex manipulation, Cx algebra, coercion optics,
`over`, `reps`/`coreps`, and `representing`/`corepresenting`. These
belong with the code that uses them.

## Target decomposition

### → `Data.Profunctor.Optic.Traversal` (Traversing/Cotraversing/Arrow)

```
arr, coarr
(***), (&&&), (<<*>>), liftR2
(+++), (|||)
divide, divideWith, cochoose, cochooseWith
choose, chooseWith, codivide, codivideWith
pappend
```

These all require `Traversing1` or `Cotraversing1` and are the
profunctor analogues of Arrow/Divisible. They belong with traversals.

Once moved, distribute them into the existing section structure rather
than keeping them in a separate "Arrow-style combinators" section:

- `arr`, `(***)`, `(&&&)`, `(<<*>>)`, `liftR2`, `pappend`, `divide`,
  `divideWith`, `cochoose`, `cochooseWith` → **Traversal Constructors**
  (they require `Traversing1`, the primal constraint)
- `coarr`, `(+++)`, `(|||)`, `choose`, `chooseWith`, `codivide`,
  `codivideWith` → **Cotraversal Constructors**
  (they require `Cotraversing1`, the dual constraint)

### → `Data.Profunctor.Optic.Index` (new module)

```
-- Constructors
ixmap, cxmap
representing, ixrepresenting
corepresenting, cxrepresenting

-- Cx algebra
cxjoin, cxreturn, cxunit, cxstrength

-- Index composition
(%), reix, ixsum, ixany, ixhead, ixlast
(#), recx, cxsum

-- Operators
ixover, cxover
reps, ixreps, coreps, cxreps
```

This is everything that manipulates indices/coindices or works through
`Representable`/`Corepresentable` directly. Currently scattered across
Combinator.hs but forms a coherent unit.

### → `Data.Profunctor.Optic.Import` (general utilities)

```
star, unstar, costar, uncostar
constL, constR
shiftedL, shiftedR
coercedL, coercedR
over
```

These are basic profunctor utilities with no optic-family dependency.
`over` is `id` at `(->)` and belongs with the foundational imports.

## Migration plan

1. Create `Data.Profunctor.Optic.Index` with the index/coindex exports
2. Move Traversing/Arrow combinators to Traversal.hs
3. Move utilities to Import.hs
4. Update `Data.Profunctor.Optic` hub module to import Index instead of Combinator
5. Make Combinator.hs a thin re-export shim (for one release cycle) or remove immediately
6. Update all downstream imports (Fold.hs, Setter.hs, View.hs, Infix.hs, container modules, test modules)
7. Update cabal exposed-modules

## Fix `(-)` type operator and normalize Fold.hs usage

The hyphenation operator is currently `type (g - f) a = f (g a)` (outer
functor on the left, applied second). Redefine to `type (f - g) a = f (g a)`
(read left-to-right: apply `g` then `f`). Then sweep Fold.hs to use `(-)`
consistently — it's currently applied in some signatures but not others.

## Move Sort type/API from Carrier.hs to Sort.hs

The `Sort` newtype, `runSort`, and all Sort combinators (`(%.)`,
`bindSort`, `catSort`, `sortC`, `remapSort`, `eitherSort`,
`maybeSort`, `zipsSorting`) currently live in Carrier.hs. Move them
to Sort.hs where they belong. Sort.hs currently re-exports them
from Carrier — make Sort.hs the defining module and have Carrier
re-export (or drop the re-export since Sort.hs is exposed).

## Remove L suffixes from Sort operators

The lens-based sort operators all have an `L` suffix (`sortingOfL`,
`groupingOfL`, `nubbingOfL`, `toMapOfL`, `countingOfL`, `foldSortingL`,
`foldSorting1L`, `mconcatSortingL`, `mergingOfL`, `innerMergeL`,
`outerMergeL`, `leftMergeL`, `rightMergeL`, `sortingDescOfL`).

The `L` suffix was presumably to distinguish from hypothetical
non-lens versions, but there are none. Remove the suffix for v1.0.0:

| Current | New |
|---|---|
| `sortingOfL` | `sorts` |
| `sortingDescOfL` | `sortsDesc` |
| `groupingOfL` | `groups` |
| `nubbingOfL` | `nubs` |
| `toMapOfL` | `toMapOf` |
| `countingOfL` | `countsOf` |
| `foldSortingL` | `foldSorts` |
| `foldSorting1L` | `foldSorts1` |
| `mconcatSortingL` | `mconcatSorts` |
| `mergingOfL` | `merges` |
| `innerMergeL` | `innerMerges` |
| `outerMergeL` | `outerMerges` |
| `leftMergeL` | `leftMerges` |
| `rightMergeL` | `rightMerges` |

Also rename in Map.Optic and IntMap.Optic which use these.

## Risk

- `over` is imported everywhere. Moving it to Import.hs means it's
  available transitively, which should be seamless.
- The `(%)` and `(#)` operators have specific fixity declarations
  that must move with them.
- `Infix.hs` imports from Combinator — need to trace dependencies.

## Files affected

- `src/Data/Profunctor/Optic/Combinator.hs` — removed
- `src/Data/Profunctor/Optic/Index.hs` — new
- `src/Data/Profunctor/Optic/Traversal.hs` — gains Arrow/Divisible combinators
- `src/Data/Profunctor/Optic/Import.hs` — gains utilities + `over`
- `src/Data/Profunctor/Optic.hs` — hub module, update re-exports
- `profunctor-optics.cabal` — update exposed-modules
- All modules that import Combinator

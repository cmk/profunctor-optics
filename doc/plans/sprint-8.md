# Sprint 8 — Move Sort to profunctor-optics core

## Scope

Move SortF into `Data.Profunctor.Optic.Carrier` as `Sort`, alongside
the existing carriers (IsoRep, LensRep, PrismRep, etc.). Rename
SortF → Sort. Update profunctor-optics-sort to import from core.

## Rationale

Sort is a legitimate carrier — `Costar (Compose ((->) i) ((,) k))` —
with the same status as `Index`, `Coindex`, and `Conjoin`. It belongs
in the core carrier module, not in a downstream package.

## Stories

| ID    | Module / target                | Description                                    |
|-------|--------------------------------|------------------------------------------------|
| S8.1  | Data.Profunctor.Optic.Carrier  | Add Sort type + DerivingVia instances           |
| S8.2  | Data.Profunctor.Optic.Carrier  | Add ASortF reified type, withSort extractor     |
| S8.3  | Data.Profunctor.Optic.Carrier  | Add runSort, Category, Choice instances         |
| S8.4  | Data.Profunctor.Optic.Types    | Add Sort-related optic type aliases if needed   |
| S8.5  | profunctor-optics-sort         | Update imports to use core Sort                 |
| S8.6  | Tests                          | Verify all 59 props still pass                  |

## New in Carrier.hs

```haskell
-- | An indexed continuation profunctor for discrimination.
--
-- @Sort i k a b = (i -> (k, a)) -> b@
--
-- The indexed generalization of Fmt from stringfmt:
-- @Fmt m a b = Sort m () a b@
--
-- @Sort@ is @Costar (Compose ((->) i) ((,) k))@. Instances
-- derive via this representation.
newtype Sort i k a b = Sort { unSort :: (i -> (k, a)) -> b }
  deriving (Functor, Applicative, Monad)
    via Costar (Compose ((->) i) ((,) k)) a
  deriving (Profunctor, Closed, Costrong, Cochoice)
    via Costar (Compose ((->) i) ((,) k))

-- Hand-rolled (needs Coapplicative on Corep):
instance Monoid i => Choice (Sort i k)

-- Cosieve / Corepresentable
instance Cosieve (Sort i k) (Compose ((->) i) ((,) k))
instance Corepresentable (Sort i k)

-- Category (needs Monoid i for id)
instance Monoid i => Category (Sort i k)

runSort :: Sort i k a b -> (i -> (k, a)) -> b

-- Reified Sort optic
type ASort i k s t a b = Sort i k a b -> Sort i k s t

-- Extractor (like withLens, withPrism)
withSort :: ASort i k s t a b -> ((i -> (k, s)) -> (i -> (k, a)) -> b) -> ...
-- Note: withSort may not be useful since Sort is already a function.
-- The extractor for Costar-shaped types is just runSort.
```

## Migration

profunctor-optics-sort renames:
- `SortF` → re-export `Sort` from core
- `runSortF` → `runSort`
- `mkSortF` / `mkSortFN` → same names, in profunctor-optics-sort
- All operators unchanged, just import path changes

## Key files

- `profunctor-optics/src/Data/Profunctor/Optic/Carrier.hs` — primary target
- `profunctor-optics/profunctor-optics.cabal` — may need `transformers` for Compose
- `profunctor-optics-sort/src/Data/Profunctor/Sort.hs` — update imports
- `profunctor-optics-sort/src/Data/Profunctor/Optic/Sort.hs` — update imports

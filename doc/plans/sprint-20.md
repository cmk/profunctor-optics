# Sprint 20 — Adjunction-based constructors and Star/Costar lifting

## Scope

Implement `alower`/`aupper` and related adjunction-based constructors
using the current optics hierarchy. These witness the Star/Costar
(Co) duality concretely when an adjunction `f ⊣ u` is available,
complementing the free `Co` construction in Dual.hs.

## Rationale

The `Co` type in Dual.hs freely adjoins `Closed` to any profunctor,
but this is a one-directional, lossy transformation. When an actual
adjunction `f ⊣ u` exists between functors, `alower`/`aupper` can
convert between Star and Costar optics *without loss* — the
adjunction provides the inverse that `Co` lacks.

This is the concrete counterpart to `adjuncted :: Iso (f a -> b) ...
(a -> u b) ...` in Iso.hs, lifted to the optic level.

## Background

These functions originate from the `wip/adjoint` branch (commit
4a76556, March 2020), which defined `Setter = Adjoint`. The current
library uses a different Setter definition (`Affine + Traversing +
Mapping`), but the adjunction-based constructors are orthogonal
and implementable using the existing `representing`/`corepresenting`
and `adjuncted`.

### Existing infrastructure

Already in the codebase:

- `representing :: Representable p => ((a -> Rep p b) -> s -> Rep p t) -> Optic p s t a b`
- `corepresenting :: Corepresentable p => ((Corep p a -> b) -> Corep p s -> t) -> Optic p s t a b`
- `reps :: Representable p => Optic p s t a b -> ((a -> Rep p b) -> s -> Rep p t)`
- `coreps :: Corepresentable p => Optic p s t a b -> ((Corep p a -> b) -> Corep p s -> t)`
- `traverseOf :: ATraversal f s t a b -> (a -> f b) -> s -> f t`
- `cotraverseOf :: ACotraversal f s t a b -> (f a -> b) -> f s -> t`
- `adjuncted :: Adjunction f u => Iso (f a -> b) (f s -> t) (a -> u b) (s -> u t)`

## TODO: setter alternate implementation

The old branch's `sec` and the current `setter` are definitionally
equal after inlining (`represent collect` = `representing (\f ->
distribute . fmap f)`). Add the alternate `sec`-style implementation
to the Haddocks of `setter` for reference, and benchmark both to
confirm identical Core.

## Stories

| ID | Target | Description |
|---|---|---|
| S20.1 | Setter.hs or Dual.hs | `aupper`: SEC to Star optic via Representable |
| S20.2 | Setter.hs or Dual.hs | `alower`: SEC to Costar optic via Adjunction |
| S20.3 | Setter.hs or Dual.hs | `adjointl`: construct optic from adjunction-quantified Costar VL |
| S20.4 | Setter.hs or Dual.hs | `adjointr`: construct optic from adjunction-quantified Star VL |
| S20.5 | Setter.hs or Dual.hs | `lifts`: convert Costar optic to Star via adjunction |
| S20.6 | Setter.hs or Dual.hs | `lowers`: convert Star optic to Costar via adjunction |
| S20.7 | Dual.hs | Document `adjuncted` as the concrete Co witness |
| S20.8 | Property.hs | Property predicates for adjunction round-trips |
| S20.9 | Test/Carrier.hs | Hedgehog tests for adjunction-based constructors |
| S20.10 | TBD | Decide module placement (Setter.hs, Dual.hs, or new Adjoint.hs) |

## S20.1 — `aupper`

Lift a SEC (semantic editor combinator) into a Star optic:

```haskell
aupper :: Representable u => ((a -> b) -> s -> t) -> Optic (Star u) s t a b
aupper f = Star #. (\afb s -> tabulate $ \i -> f (flip index i . afb) s) .# runStar
```

`aupper` takes a plain function transformer and lifts it into the
Star/Representable world. This is the "upper" adjoint — it goes
from `(->)` (the simplest profunctor) to `Star u`.

## S20.2 — `alower`

Lift a SEC into a Costar optic via an adjunction:

```haskell
alower :: Adjunction l u => ((a -> b) -> s -> t) -> Optic (Costar l) s t a b
alower = Costar #. over adjuncted . runStar .# aupper
```

`alower` composes `aupper` with `adjuncted` to go from Star to
Costar. This is the "lower" adjoint — it uses the adjunction to
cross the Star/Costar boundary.

The composition `alower = acostar . over adjuncted . stars . aupper`
makes the path explicit: SEC → Star u → adjunct → Costar l.

## S20.3 — `adjointl`

Construct an optic from a Costar-flavored adjunction-quantified VL:

```haskell
adjointl :: (forall l u. Adjunction l u => (a -> u b) -> l s -> t) -> Adjoint s t a b
adjointl f = corepresenting $ f . leftAdjunct
```

Where `Adjoint` is either a type alias or whatever the appropriate
optic type is in the current hierarchy. Needs investigation — may
be `Setter` or a new type.

## S20.4 — `adjointr`

Construct an optic from a Star-flavored adjunction-quantified VL:

```haskell
adjointr :: (forall l u. Adjunction l u => (l a -> b) -> s -> u t) -> Adjoint s t a b
adjointr f = representing $ f . rightAdjunct
```

## S20.5 — `lifts`

Convert a Costar optic to a Star optic using an adjunction:

```haskell
lifts :: Adjunction l u => Optic (Costar l) s t a b -> (l a -> b) -> s -> u t
lifts o f = leftAdjunct $ coreps o f
```

## S20.6 — `lowers`

Convert a Star optic to a Costar optic using an adjunction:

```haskell
lowers :: Adjunction l u => Optic (Star u) s t a b -> (a -> u b) -> l s -> t
lowers o f = rightAdjunct $ reps o f
```

## S20.7 — Document `adjuncted` as the concrete Co witness

Add documentation to `adjuncted` in Iso.hs and cross-references in
Dual.hs explaining that `adjuncted` is the concrete, invertible
version of the `Co` duality when an adjunction is available.

```
Co    : freely adjoins Closed, one-directional, lossy
adjuncted : Iso between Star/Costar VL forms, invertible, lossless
            (requires Adjunction f u)
```

## S20.8 — Property predicates

```haskell
-- | aupper/alower round-trip via adjunction
roundtrip_aupper_alower :: (Eq t, Adjunction l u)
  => ((a -> b) -> s -> t) -> (a -> b) -> l s -> Bool

-- | alower/aupper round-trip via adjunction
roundtrip_alower_aupper :: (Eq t, Adjunction l u)
  => ((a -> b) -> s -> t) -> (a -> b) -> s -> Bool

-- | lifts/lowers round-trip
roundtrip_lifts_lowers :: (Eq t, Adjunction l u)
  => Optic (Star u) s t a b -> (a -> u b) -> l s -> Bool

-- | adjuncted iso round-trip
roundtrip_adjuncted :: (Eq b, Adjunction l u)
  => (l a -> b) -> l a -> Bool
```

## S20.9 — Hedgehog tests

Test using concrete adjunctions:

- `(,) e ⊣ (->) e` (the canonical adjunction)
- `Identity ⊣ Identity` (trivial adjunction)

```haskell
prop_aupper_alower_roundtrip :: Property
prop_alower_aupper_roundtrip :: Property
prop_lifts_lowers_roundtrip :: Property
prop_adjuncted_roundtrip :: Property
```

## Open questions

1. **Module placement**: Should `aupper`/`alower`/`adjointl`/`adjointr`
   live in Setter.hs (where the old branch had them), Dual.hs (since
   they witness the Star/Costar duality), or a new Adjoint.hs module?

2. **`Adjoint` type alias**: The old branch defined `Adjoint s t a b`
   as a type alias — what should it be in the current hierarchy?
   Likely `Setter` or possibly a weaker type. Needs investigation
   into which constraints `adjointl`/`adjointr` actually produce.

3. **Interaction with `Co`**: Can `Co` be defined in terms of
   `alower`/`aupper` for a specific adjunction, or are they
   fundamentally different constructions? `Co` is free (works for
   any `p`), while `alower`/`aupper` are concrete (require a
   specific `f ⊣ u`).

## Dependencies

- `Data.Functor.Adjunction` from the `adjunctions` package
  (already a dependency via `distributive`)
- All existing infrastructure listed above

## Key files

- `profunctor-optics/src/Data/Profunctor/Optic/Dual.hs`
- `profunctor-optics/src/Data/Profunctor/Optic/Iso.hs` (adjuncted)
- `profunctor-optics/src/Data/Profunctor/Optic/Setter.hs`
- `profunctor-optics/src/Data/Profunctor/Optic/Combinator.hs` (representing, reps)
- `profunctor-optics/src/Data/Profunctor/Optic/Property.hs`
- `profunctor-optics/test/Test/Carrier.hs`

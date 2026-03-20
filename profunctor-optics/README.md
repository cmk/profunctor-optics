[![Haddocks](https://img.shields.io/badge/docs-haddocks-blue)](https://cmk.github.io/profunctor-optics/profunctor-optics/)
[![CI](https://github.com/cmk/profunctor-optics/actions/workflows/ci.yml/badge.svg)](https://github.com/cmk/profunctor-optics/actions/workflows/ci.yml)
[![Hackage](https://img.shields.io/hackage/v/profunctor-optics.svg)](https://hackage.haskell.org/package/profunctor-optics)

# profunctor-optics

This package provides utilities for creating and manipulating profunctor-based optics. Some highlights:

  * Full complement of isos, prisms, lenses, grates, affines, traversals, cotraversals, views, setters, folds, and more.

  * Composable indexed and co-indexed variants of most of the above.

  * Compact & straight-forward implementation. No inscrutable internal modules, lawless or otherwise ancillary typeclasses, or heavy type-level machinery. The language extensions doing the majority of the work are `RankNTypes` and `QuantifiedConstraints`.

  * Fully interoperable. All that is required to create optics (standard, indexable, or co-indexable) is the `profunctors` package. Optics compose with `(.)` from `Prelude` as is typical. If you want to provide profunctor optics for your own types in your own libraries, you can do so without incurring a dependency on this package. Conversions to & from the Van Laarhoven representations are provided for each optic type.

  * Well-documented properties and exportable predicates for testing your own optics (see `Data.Profunctor.Optic.Property`).


If you're new to profunctors, [this talk](https://www.youtube.com/watch?v=OJtGECfksds) by Phil Freeman and the following series are good general introductions:

- [Don't Fear the Profunctor Optics, part 1](https://github.com/hablapps/DontFearTheProfunctorOptics/blob/master/Optics.md)
- [Don't Fear the Profunctor Optics, part 2](https://github.com/hablapps/DontFearTheProfunctorOptics/blob/master/Profunctors.md)
- [Don't Fear the Profunctor Optics, part 3](https://github.com/hablapps/DontFearTheProfunctorOptics/blob/master/ProfunctorOptics.md)

For the more mathematically inclined, [this post](http://blog.sigfpe.com/2011/07/profunctors-in-haskell.html) by Dan Piponi is great. Oleg Grenrus also has several excellent blog posts (notably [this one](http://oleg.fi/gists/posts/2017-04-18-glassery.html)) that provide a synthesis of the Pickering, Gibbons, and Wu paper for Haskellers.

The theory behind profunctor optics is well-described in the following papers:

- [Profunctor Optics: Modular Data Accessors](https://arxiv.org/abs/1703.10857) by Pickering, Gibbons, and Wu
- [What You Needa Know about Yoneda](https://www.cs.ox.ac.uk/jeremy.gibbons/publications/proyo.pdf) by Gibbons and Boisseau

`profunctor-optics` is based on prior work by: Ed Kmett, Russell O'Connor, Twan van Laarhoven, and many others. Several papers, posts, and talks by Jeremy Gibbons, Matthew Pickering, Oleg Grenrus, Guillaume Boisseau, and others were also invaluable.


## Carrier Types

Carriers serve one purpose: **monomorphize a polymorphic optic so it can be passed as a regular value**.

A polymorphic optic like `Lens s t a b = forall p. Strong p => p a b -> p s t` can't be stored in a data structure or passed to a function that needs to use it multiple times — the `forall p` prevents this. Carriers solve this by picking a *specific* profunctor `p` that is just strong enough to extract the optic's characterizing data:

| Optic | Carrier profunctor | What it captures |
|---|---|---|
| `Iso` | `IsoRep a b` | `(s -> a, b -> t)` — both directions |
| `Prism` | `PrismRep a b` | `(s -> t+a, b -> t)` — matcher + constructor |
| `Lens` | `LensRep a b` | `(s -> a, s -> b -> t)` — getter + setter |
| `Colens` | `ColensRep a b` | `((s->a)->b) -> t` — the grate function |
| `Traversal0` | `AffineRep a b` | `(s -> t+a, s -> b -> t)` — optional match + setter |
| `Cotraversal0` | `CoaffineRep a b` | CPS encoding of `((s->t+a)->b)->t` |
| `Traversal` | `Star f` | `a -> f b` lifted to `s -> f t` |
| `Cotraversal` | `Costar f` | `f a -> b` lifted to `f s -> t` |
| `Fold` | `Star (Const r)` | Read-only traversal collecting into monoid `r` |
| `Setter` | `Star Identity` | Traversal specialized to pure mapping |
| `View` | `Star (Const a)` (= `Forget a`) | Pure getter |
| `Review` | `Tagged` | Pure constructor (ignores input) |

Each carrier profunctor has exactly the instances needed to accept the optic. E.g. `LensRep` is `Strong` but not `Choice`, so it accepts lenses but rejects prisms. The `with*` functions (e.g. `withLens`, `withPrism`) then pattern-match on the carrier to extract the characterizing functions.

The `A`-prefixed types are just the monomorphized aliases: `ALens s t a b = Optic (LensRep a b) s t a b`.

## Operator Patterns

There are four recurring patterns in the construction of operators:

### Pattern 1: Instantiate carrier, extract, apply

The operator picks the right carrier, feeds it through the optic, and deconstructs the result. This is the `with*` pattern:

```haskell
-- Feed identity values through the carrier, pattern match
withLens o f = case o (LensRep id (flip const)) of LensRep x y -> f x y
withPrism o f = case o (PrismRep Right id) of PrismRep g h -> f g h
```

Then operators like `view` and `review` are thin wrappers:

```haskell
view    o = asks $ folds o id       -- folds uses Star (Const r)
review  o = reviews o id            -- reviews uses Tagged
reviews o f = f . unTagged #. o .# Tagged
```

### Pattern 2: Wrap in functor carrier, run optic, unwrap

Most operators that *do* something (traverse, set, fold) work by wrapping a user function in the appropriate `Star`/`Costar`/`Const`/`Identity` carrier, running the optic, then unwrapping:

```haskell
-- Setter: wrap in Identity, traverse, unwrap
sets o = (runIdentity #.) #. traverses o .# (Identity #.)

-- Reset: wrap in Identity, cotraverse, unwrap
resets o = (.# Identity) #. cotraverses o .# (.# runIdentity)

-- Fold: wrap in Const, traverse, extract
folds o f = getConst #. traverses o .# (Const #. f)
```

The `traverses` and `cotraverses` functions are themselves just running `Star`/`Costar`:

```haskell
traverses o f = runStar (o (Star f))     -- (**~)
cotraverses o f = runCostar (o (Costar f))  -- (//~)
```

### Pattern 3: Layering with MonadReader/MonadState/MonadWriter

Once a pure operator exists, the mtl variants are mechanical lifts:

```haskell
view  o     = asks $ folds o id      -- Reader
use   o     = gets (view o)          -- State
(.=)  o b   = modify (o .~ b)        -- State
(..=) o f   = modify (o ..~ f)       -- State
locally o f = Reader.local (o ..~ f)  -- Reader
scribe o b  = tell (mempty & o .~ b) -- Writer
```

### Pattern 4: Indexed variants curry/uncurry the index

Indexed operators thread a `(k, a)` pair through where plain operators thread `a`. The conversion is always the same shape — curry/uncurry + `mempty` seed:

```haskell
setsWithKey o f     = curry (sets o $ uncurry f) mempty
resetsWithKey o f   = flip (resets o $ flip f) mempty
setWithKey o        = setsWithKey o . (const .)
```

The `mempty` initializes the monoidally-accumulated index.

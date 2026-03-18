# profunctor-optics-folds

Moore and Mealy machines as profunctor optics, with strict
left folds (`Foldl`/`Foldl1`).

## Overview

This package provides streaming fold abstractions built on
profunctor optics:

1. **Moore machines** — state machines that observe input
   element-by-element and produce accumulated output
2. **Mealy machines** — like Moore but output depends on
   both state and current input
3. **Strict left folds** (`L`, `L1`) — Tekmo-style folds
   integrated with profunctor optics

## Moore machines (cofolds)

### Theory

A **Moore machine** is a comonadic state machine: it has a
current output and transitions on input. In optics terms,
a Moore machine is a **cofold** — the dual of a fold.

Where a fold *consumes* structure (traversal → monoid),
a cofold *produces* structure (cotraversal → comonoid).

```haskell
moore :: (x -> a -> x) -> x -> (x -> b) -> Moore a b
```

This is "seed + step + extract" — the same shape as `Nu`
(greatest fixed point), making Moore machines naturally
codata.

### Simple example: running sum

```haskell
import Data.Profunctor.Optic.Machine

-- A Moore machine that tracks a running sum:
>>> let m = moore (+) 0 id
>>> listing m [1, 2, 3, 4, 5]
[0, 1, 3, 6, 10, 15]
```

### Complex example: fold with projection

```haskell
import Data.Profunctor.Optic.Machine

-- Find the minimum, with a default:
>>> minimizedDef 0 [3, 1, 4, 1, 5]
1
>>> minimizedDef 0 []
0

-- Fold over projected values:
>>> projected fst (foldingl (+) 0) [(1,"a"), (2,"b"), (3,"c")]
6
```

## Strict left folds (L / L1)

### Theory

`L a b` (a strict left fold from `a` to `b`) is the
profunctor representation of Tekmo's `Foldl`:

```haskell
type L a b = Foldl a b
-- internally: Foldl step initial extract
```

Folds are `Applicative` — you can combine independent
folds to run in a single pass:

```haskell
(,) <$> sum <*> length  -- sum and length in one pass
```

### Simple example: basic folds

```haskell
import Data.Profunctor.Rep.Foldl

>>> run sum [1, 2, 3]
6
>>> run list [1, 2, 3]
[1, 2, 3]
>>> run (liftA2 (/) sum (fmap fromIntegral length)) [1, 2, 3, 4]
2.5
```

### Complex example: windowed fold

```haskell
import Data.Profunctor.Rep.Foldl

-- Prefix takes the first n elements:
>>> run (prefix 3 list) [1, 2, 3, 4, 5]
[1, 2, 3]

-- Prescan gives running fold results:
>>> run (prescan sum list) [1, 2, 3, 4]
[0, 1, 3, 6]
```

## Non-empty folds (L1)

### Theory

`L1 a b` is a fold that requires at least one element.
It uses `Semigroup` instead of `Monoid`, and `Foldable1`
instead of `Foldable`.

```haskell
>>> run1 head (1 :| [2, 3])
1
>>> run1 last (1 :| [2, 3])
3
>>> run1 minimum (3 :| [1, 4, 1, 5])
1
```

## Modules

| Module | Contents |
|---|---|
| `Data.Profunctor.Optic.Machine` | `moore`, `mealy`, `listing`, `foldingl`/`foldingr`, `projected`, `minimized`/`maximized` |
| `Data.Profunctor.Rep.Foldl` | `L`, `run`, `foldl`, `prefix`, `prescan`, `postscan`, `list`, `mconcat`, `headDef`, `lastDef`, `sum`, etc. |
| `Data.Profunctor.Rep.Foldl1` | `L1`, `run1`, `foldl1`, `head`, `last`, `minimum`, `maximum`, `sconcat` |

## Dependencies

```
base, profunctor-optics
```

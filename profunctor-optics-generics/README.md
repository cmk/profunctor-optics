# profunctor-optics-generics

Newtype-based optics via `Coercible`.

## Overview

Provides `wrapped` and `ala` for working with newtypes
through profunctor optics, using GHC's `Coercible`
constraint for zero-cost conversions.

## Iso for newtypes

### Theory

Every newtype `N` is isomorphic to its underlying type `A`.
The `Coercible` constraint witnesses this at zero runtime
cost. `wrapped` lifts this into an `Iso`:

```haskell
wrapped :: (Coercible s a, Coercible t b) => Iso s t a b
```

### Simple example: wrapping and unwrapping

```haskell
import Data.Profunctor.Optic.Newtype
import Data.Profunctor.Optic
import Data.Monoid (Sum(..))

>>> view wrapped (Sum 42)
42
>>> review wrapped 42 :: Sum Int
Sum {getSum = 42}
```

### Complex example: ala

```haskell
import Data.Profunctor.Optic.Newtype
import Data.Monoid

-- ala lifts a function to work "under" a newtype:
-- ala Sum foldMap [1, 2, 3]  ≡  getSum (foldMap Sum [1, 2, 3])

>>> ala @(Sum Int) foldMap [1, 2, 3]
6
>>> ala @(Product Int) foldMap [1, 2, 3]
6
```

### Rewrapping

`rewrapped` converts between two newtypes that wrap the
same underlying type:

```haskell
>>> review (rewrapped @(Sum Int)) (Product 42) :: Sum Int
Sum {getSum = 42}
```

## Modules

| Module | Contents |
|---|---|
| `Data.Profunctor.Optic.Newtype` | `wrapped`, `rewrapped`, `rewrapped'`, `ala` |

## Dependencies

```
base, profunctor-optics
```

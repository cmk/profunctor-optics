[![Haddocks](https://img.shields.io/badge/docs-haddocks-blue)](https://cmk.github.io/profunctor-optics/profunctor-optics-th/)
[![CI](https://github.com/cmk/profunctor-optics/actions/workflows/ci.yml/badge.svg)](https://github.com/cmk/profunctor-optics/actions/workflows/ci.yml)

# profunctor-optics-th

Template Haskell generation of profunctor optics from
record types.

## Overview

Automatically derive lenses, prisms, traversals, and
other optics from data type declarations using
Template Haskell.

## Deriving lenses

### Theory

A **lens** focuses on exactly one field of a product type.
For a record with fields, each field naturally gives rise
to a lens. Template Haskell automates the boilerplate.

### Example 1: record lenses

```haskell
{-# LANGUAGE TemplateHaskell #-}
import Data.Profunctor.Optic.TH

data Person = Person
    { _personName :: String
    , _personAge  :: Int
    }

makeFieldOptics defaultFieldRules ''Person

-- Generates:
-- personName :: Lens' Person String
-- personAge  :: Lens' Person Int

>>> view personName (Person "Alice" 30)
"Alice"
>>> set personAge 31 (Person "Alice" 30)
Person "Alice" 31
```

### Example 2: sum type prisms

```haskell
{-# LANGUAGE TemplateHaskell #-}
import Data.Profunctor.Optic.TH

data Shape
    = Circle Double
    | Rectangle Double Double
    | Triangle Double Double Double

makeFieldOptics defaultFieldRules ''Shape

-- Generates prisms for each constructor
```

## Modules

| Module | Contents |
|---|---|
| `Data.Profunctor.Optic.TH` | `makeFieldOptics`, `defaultFieldRules`, `makePrismOptics` |

## Dependencies

```
base, profunctor-optics, template-haskell, th-abstraction
```

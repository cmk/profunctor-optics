# profunctor-optics-exceptions

Profunctor optics for Haskell's exception hierarchy.

## Overview

This package provides prism-based access to exceptions,
enabling type-safe exception matching, throwing, and
catching via the profunctor optics vocabulary.

## Prisms for exceptions

### Theory

Exceptions form a sum type hierarchy rooted at
`SomeException`. A **prism** is the natural optic for
sum types — it can match (review) one branch and inject
(preview) into it:

```
Prism s t a b = forall p. Choice p => p a b -> p s t
```

For exceptions: `exception :: Exception e => Prism' SomeException e`
lets you match on a specific exception type within the
`SomeException` sum.

### Simple example: matching exceptions

```haskell
import Control.Exception.Optic
import Control.Exception (IOException, SomeException)
import Data.Profunctor.Optic

-- Match an IOException from a SomeException:
>>> let e = toException (userError "oops") :: SomeException
>>> preview exception e :: Maybe IOException
Just user error (oops)

-- Inject an exception:
>>> review exception (userError "oops") :: SomeException
user error (oops)
```

### Complex example: safe exception handling

```haskell
import Control.Exception.Optic
import Data.Profunctor.Optic

-- catches_ runs an IO action and handles matching exceptions:
>>> catches_ [handles_ exception (\(e :: IOException) -> putStrLn "IO!")] (readFile "/nonexistent")
IO!

-- Distinguish sync from async exceptions:
>>> tries (sync . exception @IOException) (readFile "/nonexistent")
Left user error (...)

-- Access IOException fields:
>>> preview ioeDescription (userError "oops")
Just "oops"
```

## Co-prisms (reviews)

### Theory

The dual of a prism is a **review** — where a prism can
both match and inject, a review can only inject. This is
useful for constructing exceptions:

```haskell
throws :: Exception e => e -> IO a
throws = throw . review exception
```

### Simple example: typed throwing

```haskell
import Control.Exception.Optic

-- throws_ ignores the return and throws:
>>> throws_ (userError "boom")
*** Exception: user error (boom)
```

## Modules

| Module | Contents |
|---|---|
| `Control.Exception.Optic` | `exception`, `sync`, `async`, `throws`, `tries`, `catches`, `handles`, `masked`, `exmapped`, IOException field optics |

## Dependencies

```
base, profunctor-optics
```

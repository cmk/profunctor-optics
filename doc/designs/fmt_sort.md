# Design: Sort and profunctor-optics-{containers, strings, folds, sequences}

See also [README.md](../README.md) for the user-facing overview.
This document covers the theoretical underpinnings.

## Core types

```haskell
newtype Fmt m a b = Fmt { unFmt :: (m -> a) -> b } -- upstream in stringfmt

newtype Sort1 k a b = Sort1 { runSort1 :: NonEmpty (k, a) -> [NonEmpty b] } -- local prototype

newtype Sort2 k a b = Sort2 { runSort2 :: NonEmpty (k, a) -> NonEmpty [b] } -- local prototype

newtype Sort3 i j k a b = Sort3 { runSort3 :: (i -> (k, a)) -> j -> k -> b } -- local prototype
```

`Fmt m` is `Costar ((->) m)` from `profunctors`, giving `Profunctor`,
`Closed`, `Costrong`, `Cochoice`, `Category`, and `Arrow` instances
for free. It is `Cosieve` with `(->) m` and `Corepresentable` with
`Corep (Fmt m) = (->) m`.

`(->) m` is `Distributive` (representable with `Rep = m`), so
`Costar ((->) m)` is the canonical profunctor for cotraversals and
grates.

## Fmt and Yoneda

```
Fmt m a a  =  (m -> a) -> a        -- for a specific a
forall a. (m -> a) -> a  ≅  m      -- by Yoneda
```

A universally-quantified `Fmt m a a` collapses to `m`. The whole
point of `Fmt` is that it does *not* universally quantify — the
index `b` carries argument structure:

```
Fmt1 m s a     =  Fmt m s (a -> s)          -- one hole
Fmt2 m s a b   =  Fmt m s (a -> b -> s)     -- two holes
```

## Fmt and Day convolution

`(%)` is Day convolution of `(->) m`. Each format hole adds a
Day factor:

```
Day ((->) m) ((->) m) a  ≅  m -> m -> a    -- by co-Yoneda
```

So `Fmt1`, `Fmt2`, `Fmt3` are 1-, 2-, 3-fold Day convolutions.
Day's monoidal laws give free laws for `%`:

- Associativity: `(f % g) % h = f % (g % h)`
- Unit: `fmt mempty % f = f`

The `Curried`/`Day` adjunction (`Day f -| Curried f`) is what makes
the `Closed` instance work.

## Fixed points

From [data-fix](https://hackage.haskell.org/package/data-fix):

| Type | Encoding | Good at |
|---|---|---|
| `Mu f` | Church (CPS) | Folding — O(1) catamorphism |
| `Fix f` | Explicit | Pattern matching, Eq/Ord/Show/Hashable/NFData |
| `Nu f` | Existential | Unfolding — O(1) anamorphism, codata |

### Mu and Fmt

`Mu` and `Fmt` share the same functor `(->) m` at their core:

```
Mu ((->) m)  =  forall a. ((m -> a) -> a) -> a  ≅  m   -- by Yoneda
Fmt m a b    =  (m -> a) -> b                            -- indexed, not quantified
```

`Fmt` is `Mu ((->) m)` with the universal quantifier removed and
replaced by indexed continuation passing. Same functor, different
fixed-point strategies. `Mu` takes the fixed point (trees, streams).
`Fmt` keeps it open (indexed continuations, profunctor optics).

### Nu and codata

`Nu ((->) m)` does NOT collapse — it's the greatest fixed point,
representing infinite streams / Moore machines. This is the
complement to `Mu`'s collapse: least fixed point of `(->) m` is
trivial, greatest is infinite.

### Pattern functors for standard types

Lazy `ByteString` and `Text` are `Mu (Cons chunk)` internally:

```
Mu (Cons StrictByteString)  ≅  Lazy.ByteString
Mu (Cons StrictText)        ≅  Lazy.Text
```

The entire pretty-printer pipeline is fold/unfold on `Mu`/`Nu`:

```
Mu (Doc m ann)                        -- document tree
  → refold → [Token m ann]            -- token list (eager)
  → fold   → m                        -- rendered output

Mu (Doc m ann)                        -- document tree
  → layoutStream → Nu (Cons (Token m ann))  -- token stream (lazy)
  → renderStream → m                        -- rendered output
```

## Recursion schemes

No `Recursive`/`Corecursive` typeclasses — explicit functions on `Mu`:

| Name | Type | Use |
|---|---|---|
| `fold` | `(f a -> a) -> Mu f -> a` | All folds (flatten, fuse, reAnnotate, layout) |
| `foldWithContext` | `(f (Mu f, a) -> a) -> Mu f -> a` | changesUponFlattening (needs original subtree) |
| `foldWithAux` | `(f b -> b) -> (f (b, a) -> a) -> Mu f -> a` | Optimized group (zygomorphism) |
| `unfold` | `(a -> f a) -> a -> Mu f` | Building trees from seeds |
| `unfoldShort` | `(a -> f (Either (Mu f) a)) -> a -> Mu f` | Unfold with early termination |
| `refold` | `(f b -> b) -> (a -> f a) -> a -> b` | Layout: tree → stream, fused |
| `hoistMu` | `(forall a. f a -> g a) -> Mu f -> Mu g` | Strip/transform annotations |
| `comap` | `(Bifunctor f, ...) => (a -> b) -> Mu (f a) -> Mu (f b)` | Element map (anamorphic) |
| `elgot` | `... -> r -> b` | Unfold with short-circuit |
| `mutu` | `... -> Mu f -> c` | Mutual recursion |
| `prepro` | `... -> Mu f -> c` | Prepromorphism (transform before each step) |
| `stream` | `(i -> g i) -> (f o -> o) -> ... -> state -> i -> o` | Streaming metamorphism (generic) |

## Kan extension connections

| Kan extension | What it gives us |
|---|---|
| **Yoneda** | `runFmt . fmt = id`, fold fusion law, `hoistMu` laws |
| **Day** | Laws for `%`, `Fmt1`/`Fmt2`/`Fmt3` as iterated convolutions |
| **Curried** | The `Closed` instance / cotraversal structure on `Fmt m` |
| **Ran + Representable** | Indexed decomposition for `ShortByteString`/`ShortText` cotraversals |
| **Codensity** | `Codensity ((->) m) ≅ State m`, `Codensity (Compose ((->) m) n) ≅ StateT m n` |
| **Density** | Comonad from `Lan f f` (dual of Codensity) |

## Pattern functor: Doc

```haskell
data Doc m ann r
    = Fail | Empty | Leaf !Int !m
    | Cat r r | Line | FlatAlt r r
    | Nest !Int r | Union r r | Ann ann r
    | Column (Int -> r) | Nesting (Int -> r)
```

Changes from prettyprinter's `Doc`:

- `Char`/`Text` merged into `Leaf !Int !m` — parametric over content type
- `WithPageWidth` dropped — recoverable via `Column`/`Nesting`
- `Fail` retained — needed for lazy failure propagation through `Column`/`Nesting`
- Parametric over `m` (content type) — works with `Text`, `Builder`, `ShowS`-wrapper, etc.

`Tree m ann = Mu (Doc m ann)` is the document tree type.

## Pretty-printer operations as recursion schemes

| Operation | Scheme | Notes |
|---|---|---|
| `flatten` | `fold` | `FlatAlt _ y -> y`, `Line -> Fail` |
| `changesUponFlattening` | direct (paramorphism-like) | Needs original subtree at `Cat` |
| `group'` | uses `changesUponFlattening` | Only wraps in `Union` when flattening changes something |
| `fuse` | `fold` | Merge adjacent `Leaf` nodes, collapse nested `Nest` |
| `reAnnotate` | `hoistMu` | Map over annotations |
| `layoutPretty` | pipeline with stack | Wadler/Leijen with one-line lookahead + ribbon fraction |
| `layoutStream` | `Nu` seed + step | Same algorithm, lazy token generation |

## Module layout

```
Data.Fmt              — Re-exports: core Fmt + common Tree combinators + Code encoders
Data.Fmt.Type         — Core: Fmt type, combinators, generic formatters
Data.Fmt.Fixed        — Mu/Fix/Nu (from data-fix), recursion schemes, streaming, Pair
Data.Fmt.Functor      — Doc pattern functor, Tree type alias, instances
Data.Fmt.Tree         — Pretty-printer API: smart constructors, combinators, layout, rendering
Data.Fmt.Cons         — Cons pattern functor, fstream, iterate/repeat, distributive laws
Data.Fmt.Kan          — Kan extension connections (Day, Yoneda, Codensity, Ran, Lan, etc.)
Data.Fmt.Code         — Numeric/binary encoders (Builder-based)
Data.Fmt.ByteString   — ByteFmt, runByteFmt, printf, string operations
Data.Fmt.Text         — TextFmt, runTextFmt, string operations
Data.Fmt.String       — ShowS-backed Builder newtype, StringFmt, runStringFmt
```

## Profunctor-optics-strings (future)

The `Closed` instance on `Fmt m` gives native support for
indexed cotraversals/grates:

```
Grate s t a b  =  forall p. Closed p => p a b -> p s t

-- Instantiated at Fmt m:
((m -> a) -> b) -> ((m -> s) -> t)
```

`ShortByteString` and `ShortText` are `Representable` with `Rep = Int`
(backed by `ByteArray#`). The Kan extension connection:
`Ran ShortByteString Identity a ≅ (Int, a)` — indexed decomposition
for free. Grate laws hold by construction: `tabulate . index = id`.

The Codensity/StateT iso `Codensity (Compose u n) ≅ StateT (Rep u) n`
gives effectful indexed traversal state machines for `ShortByteString`
and `ShortText`.

Finish prototyping the Sort profunctors and integrate them.

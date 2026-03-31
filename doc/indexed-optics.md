# Indexed and Coindexed Optics

## Encoding

profunctor-optics threads indices via product/function types on the profunctor:

```haskell
type Ix p k a b = p (k, a) b          -- index on the left (product)
type Cx p k a b = p a (k -> b)         -- coindex on the right (function)

type Ixoptic p k s t a b = Ix p k a b -> Ix p k s t
type Cxoptic p k s t a b = Cx p k a b -> Cx p k s t
```

`Ix` and `Cx` are dual: the index is a product on the contravariant side,
the coindex is a function on the covariant side.

## Composition with `(.)`

Indexed and coindexed optics compose with ordinary function composition.
The index/coindex threads structurally through the profunctor:

```haskell
f :: Ixoptic p k s t b c      -- p (k,b) c -> p (k,s) t
g :: Ixoptic p k u v a b      -- p (k,a) b -> p (k,u) v
f . g :: Ixoptic p k u v a c  -- p (k,a) c -> p (k,u) v
```

The same `k` flows through both optics. For coindexed optics, the `k ->`
wrapping on the right threads identically.

### How VL-lifted optics thread the index

Van Laarhoven-style indexed optics receive the incoming index as a parameter:

```haskell
-- Ix VL signature
(k -> a -> f b) -> k -> s -> f t
--                 ^
--                 incoming index from outer composition

-- Cx VL signature
(f a -> k -> b) -> f s -> k -> t
--                        ^
--                        incoming coindex from outer composition
```

The VL lifters (`ixlensVl`, `ixtraversalVl`, `cxlensVl`, `cxtraversalVl`,
etc.) pass the incoming index through to the VL function. Each optic
decides independently what to do with it:

- **Lenses/gratings** ignore it (they produce their own index from the getter)
- **`ix`-lifted traversals** use it as the initial accumulator
- **`noix`-lifted traversals** pass it to every element unchanged

## Constructing indexed optics

### Natively indexed (profunctor combinators)

These are defined directly as profunctor transformations. The index
threads through `(k, -)` tuple rearrangement:

```haskell
ixfirst :: Ixlens k (a, c) (b, c) a b
ixfirst = lmap assocl . first
-- (k, (a, c)) --assocl--> ((k, a), c) --first--> (b, c)

ixsecond :: Ixlens k (c, a) (c, b) a b
ixsecond = lmap (\(i, (c, a)) -> (c, (i, a))) . second
```

No `Monoid` or `Semigroup` constraint. The index passes through
structurally.

### VL-lifted lenses (`ixlensVl`)

```haskell
ixlens :: (s -> (k, a)) -> (s -> b -> t) -> Ixlens k s t a b
ixlens ska sbt = ixlensVl $ \kab _k s -> sbt s <$> uncurry kab (ska s)
```

The `_k` (incoming index) is ignored because the lens produces its own
`k` via the getter `ska`.

### VL-lifted traversals (`ix`, `noix`)

```haskell
ix :: Semigroup k => k -> Traversal s t a b -> Ixtraversal k s t a b
ix k o = ixrepresenting $ \f k_in s ->
  flip evalState k_in . getCompose . flip runStar s . o . Star $ \a ->
    Compose $ (f <$> get <*> pure a) <* modify (<> k)
```

`ix` uses the incoming `k_in` as its initial accumulator (replacing the
old `mempty`). After each element it appends `k` via `(<>)`. This is why
`ix` requires `Semigroup` (relaxed from the old `Monoid`).

```haskell
noix :: Traversal s t a b -> Ixtraversal k s t a b
noix o = ixrepresenting $ \iab k_in s -> flip runStar s . o . Star $ iab k_in
```

`noix` assigns every element the incoming `k_in`. No constraints on `k`.

### Examples

Single traversal:
```haskell
>>> B.first getSum <$> ixtoListOf (ix (Sum 1) traversed) "foobar"
[(0,'f'),(1,'o'),(2,'o'),(3,'b'),(4,'a'),(5,'r')]
```

Composed with `(.)` -- indices accumulate:
```haskell
>>> ixtoListOf (ix "x" traversed . ix "o" traversed) ["foo", "bar"]
[("",'f'),("o",'o'),("oo",'o'),("x",'b'),("xo",'a'),("xoo",'r')]
```

The outer `ix "x" traversed` accumulates `"x"` per element. The inner
`ix "o" traversed` receives the accumulated index as its seed.

## Constructing coindexed optics

### VL-lifted colenses (`cxlensVl`)

```haskell
cxlens :: (((s -> a) -> k -> b) -> t) -> Cxlens k s t a b
cxlens f = cxlensVl $ \aib s _k -> f $ \sa -> aib (fmap sa s)
```

The `_k` (incoming coindex) is ignored.

### VL-lifted cotraversals (`cxtraversalVl`)

```haskell
cxtraversed :: Ord k => Cxtraversal k (Map k a) (Map k b) a b
cxtraversed = cxtraversalVl $ \fakb fs _k ->
  Map.fromSet (\k -> fakb (fmap (Map.! k) fs) k) (Map.keysSet (copure fs))
```

Container cotraversals currently ignore the incoming coindex.

## Operators

All indexed/coindexed operators seed the initial index at `mempty`:

| Operator | Carrier | Constraint |
|----------|---------|------------|
| `ixview` | `Star (Const (k,a))` | `Monoid k` |
| `ixover` | `Conjoin` | `Monoid k` |
| `ixsets` | `Star Identity` | `Monoid k` |
| `cxview` | `Tagged` | none |
| `cxover` | `Conjoin` | `Monoid i` |
| `cxsets` | `Costar Identity` | `Monoid i` |

The `Monoid` constraint on operators is the cost of supplying the initial
index without requiring the caller to provide one. For lenses, the index
comes from the getter regardless; for traversals, `mempty` is the correct
starting accumulator.

### `withIxlens` (no Monoid)

`withIxlens` extracts the getter/setter pair from a monomorphized `AIxlens`
without requiring `Monoid k`. It uses lazy knot-tying: the lens's getter
ignores its input `k` (producing its own from `s`), so we feed the output
`k` back as the input via a lazy binding:

```haskell
withIxlens :: AIxlens k s t a b -> ((s -> (k, a)) -> (s -> b -> t) -> r) -> r
withIxlens o f = case o (IxlensRep id $ flip const) of
  IxlensRep x y -> f (\s -> let ka@(k, _) = x (k, s) in ka)
                      (\s b -> let  (k, _) = x (k, s) in y (k, s) b)
```

## Comparison with lens

### Index encoding

| | lens | profunctor-optics |
|---|---|---|
| Index carrier | `Indexed i a b = i -> a -> b` (newtype) | `Ix p k a b = p (k, a) b` (product) |
| Coindex | N/A | `Cx p k a b = p a (k -> b)` (function) |
| Duality | No coindexed optics | Ix/Cx are dual |

### Operators

| | lens | profunctor-optics |
|---|---|---|
| `over` | `coerce` (zero cost) | `id` (zero cost) |
| `iover` | `coerce` (zero cost) | `Conjoin` routing + `mempty` |
| `view` | `getConst #. l Const` | `foldMapOf` |
| `iview` | `Indexed $ \i -> Const #. (,) i` | `ixfoldMapOf` |
| Monoid on index? | No (index is a callback parameter) | Yes (index must be seeded) |

lens avoids `Monoid` on the index because `Indexed i a b` is a newtype
over `i -> a -> b` -- the optic *supplies* the index to whoever consumes
it, so no seed value is needed. profunctor-optics encodes the index as a
product `(k, a)`, so operators must supply an initial `k` via `mempty`.

### Composition

| | lens | profunctor-optics |
|---|---|---|
| Keep right index | `.` / `.>` | `.` |
| Keep left index | `<.` | -- |
| Combine (tuple) | `<.>` | -- |
| Combine (custom) | `icompose f` | `.` (via `ix`/VL threading) |
| Index types | Heterogeneous (`i`, `j` -> `(i,j)`) | Homogeneous (`Semigroup k`) |

lens provides four composition strategies with arbitrary combining
functions and heterogeneous index types. profunctor-optics uses a single
mechanism: `.` threads the incoming index through VL-lifted optics, and
individual optics decide how to combine (via `Semigroup` in `ix`, or by
ignoring the incoming index in lenses).

The tradeoff: lens is more flexible (heterogeneous indices, arbitrary
combining), profunctor-optics is more uniform (one combinator, plus
Ix/Cx duality and coindexed composition for free).

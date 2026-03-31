# Sprint 26 — Text and ByteString optics: complete API coverage

## Goal

Flesh out `Data.Text.Optic` and `Data.ByteString.Optic` to cover the
full upstream API surface, then split each into strict/lazy modules.

## Current state

Each module currently exports:

| Category | Text | ByteString |
|----------|------|------------|
| Iso | `short`, `lazy`, `packed`, `utf8`, `lined`, `worded`, `splitOn` | `short`, `lazy`, `packed`, `lined`, `worded`, `splitOn` |
| Traversal | `chars` | `bytes` |
| Fold | `folded` | `folded` |
| Setter | `mapped` | `mapped` |
| Cotraversal | `zippedText` | `zippedBS` |
| Operator | `sortingText` | `sortingBS` |

## Planned additions

### Phase 1 — Star-side (Strong, Choice, Traversing)

#### Isos

| Name | Text type | ByteString type | Notes |
|------|-----------|-----------------|-------|
| `reversed` | `Iso' Text Text` | `Iso' ByteString ByteString` | `reverse`/`reverse` |
| `chunked` | `Iso' TL.Text [Text]` | `Iso' BL.ByteString [ByteString]` | Lazy only: `fromChunks`/`toChunks` |

#### Prisms

| Name | Text type | ByteString type | Notes |
|------|-----------|-----------------|-------|
| `consed` | `Prism' Text (Char, Text)` | `Prism' ByteString (Word8, ByteString)` | `uncons`/`cons` |
| `snoced` | `Prism' Text (Text, Char)` | `Prism' ByteString (ByteString, Word8)` | `unsnoc`/`snoc` |
| `prefixed` | `Text -> Prism' Text Text` | `ByteString -> Prism' ByteString ByteString` | `stripPrefix`/`(<>)` |
| `suffixed` | `Text -> Prism' Text Text` | `ByteString -> Prism' ByteString ByteString` | `stripSuffix`/flip`(<>)` |

#### Traversal0 (Affine)

| Name | Text type | ByteString type | Notes |
|------|-----------|-----------------|-------|
| `at` | `Int -> Traversal0' Text Char` | `Int -> Traversal0' ByteString Word8` | Positional lookup. Non-indexed, takes key param |
| `ixat` | `Ixtraversal0' (Sum Int) Text Char` | `Ixtraversal0' (Sum Int) ByteString Word8` | Indexed: incoming index IS the position |
| `found` | `(Char -> Bool) -> Traversal0' Text Char` | `(Word8 -> Bool) -> Traversal0' ByteString Word8` | `find` as affine traversal |

#### Fold0

| Name | Text type | ByteString type | Notes |
|------|-----------|-----------------|-------|
| `headed` | `Fold0 Text Char` | `Fold0 ByteString Word8` | `head` made total |
| `lasted` | `Fold0 Text Char` | `Fold0 ByteString Word8` | `last` made total |
| `foundIndex` | `(Char -> Bool) -> Fold0 Text (Sum Int)` | `(Word8 -> Bool) -> Fold0 ByteString (Sum Int)` | `findIndex` |
| `elemIndex` | — | `Word8 -> Fold0 ByteString (Sum Int)` | ByteString only |

#### Indexed traversals

| Name | Text type | ByteString type | Notes |
|------|-----------|-----------------|-------|
| `ixtraversed` | `Ixtraversal (Sum Int) Text Text Char Char` | `Ixtraversal (Sum Int) ByteString ByteString Word8 Word8` | Positional index, threads incoming |
| `ixfolded` | `Ixfold (Sum Int) Text Char` | `Ixfold (Sum Int) ByteString Word8` | Same |
| `ixmapped` | `Ixsetter (Sum Int) Text Text Char Char` | `Ixsetter (Sum Int) ByteString ByteString Word8 Word8` | Same |

#### Lenses (on pairs)

| Name | Text type | ByteString type | Notes |
|------|-----------|-----------------|-------|
| `split` | `Int -> Lens' Text (Text, Text)` | `Int -> Lens' ByteString (ByteString, ByteString)` | `splitAt n` as lens on pair |
| `spanned` | `(Char -> Bool) -> Lens' Text (Text, Text)` | `(Word8 -> Bool) -> Lens' ByteString (ByteString, ByteString)` | `span p` |
| `broken` | `(Char -> Bool) -> Lens' Text (Text, Text)` | `(Word8 -> Bool) -> Lens' ByteString (ByteString, ByteString)` | `break p` |
| `brokenOn` | `Text -> Lens' Text (Text, Text)` | — | `breakOn needle` (Text only) |

#### Setters / Adjoints

| Name | Text type | ByteString type | Notes |
|------|-----------|-----------------|-------|
| `filtered` | `Adjoint Text Text Char Bool` | `Adjoint ByteString ByteString Word8 Bool` | `filter` |
| `casefolded` | `Setter' Text Char` | — | `toCaseFold` (Text only) |
| `lowered` | `Setter' Text Char` | — | `toLower` (Text only) |
| `uppered` | `Setter' Text Char` | — | `toUpper` (Text only) |
| `titled` | `Setter' Text Char` | — | `toTitle` (Text only) |
| `sorted` | — | `Setter' ByteString Word8` | `sort` (ByteString only) |

### Phase 2 — Costar-side (Closed, Costrong, Coapplicative)

#### Cofolds (anamorphisms)

| Name | Text type | ByteString type | Notes |
|------|-----------|-----------------|-------|
| `unfolding` | `Cofold Text Char` | `Cofold ByteString Word8` | Via `unfoldr` |
| `unfoldingN` | `Int -> Cofold Text Char` | `Int -> Cofold ByteString Word8` | Via `unfoldrN`, bounded |

#### Colenses (grates)

| Name | Text type | ByteString type | Notes |
|------|-----------|-----------------|-------|
| `justified` | `Int -> Char -> Colens Text Text Char Char` | — | `justifyLeft` (Text only) |
| `built` | — | `Colens ByteString ByteString Builder Builder` | Via `dimap runBuilderWith builder . closed` |
| `scannedL` | `Char -> Colens Text Text Char Char` | `Word8 -> Colens ByteString ByteString Word8 Word8` | `scanl` |
| `scannedR` | `Char -> Colens Text Text Char Char` | `Word8 -> Colens ByteString ByteString Word8 Word8` | `scanr` |
| `replicated` | `Colens Text Text Text Text` | `Colens ByteString ByteString Word8 Word8` | `replicate` |

#### Coindexed optics

| Name | Text type | ByteString type | Notes |
|------|-----------|-----------------|-------|
| `cxtraversed` | `Cxtraversal (Sum Int) Text Text Char Char` | `Cxtraversal (Sum Int) ByteString ByteString Word8 Word8` | Dual of `ixtraversed` |
| `cxfolded` | `Cxfold (Sum Int) Text Char` | `Cxfold (Sum Int) ByteString Word8` | Dual of `ixfolded` |
| `cxmapped` | `Cxsetter (Sum Int) Text Text Char Char` | `Cxsetter (Sum Int) ByteString ByteString Word8 Word8` | Dual of `ixmapped` |
| `cxfiltered` | `Cxsetter (Sum Int) Text Text Char Bool` | `Cxsetter (Sum Int) ByteString ByteString Word8 Bool` | Indexed filter |

#### Cotraversals

| Name | Text type | ByteString type | Notes |
|------|-----------|-----------------|-------|
| `zipped` | exists (`zippedText`) | exists (`zippedBS`) | Rename to `zipped` for consistency |
| `zippedWith` | `Cotraversal Text Text Char Char` | `Cotraversal ByteString ByteString Word8 Word8` | `zipWith` |

### Phase 3 — Strict/Lazy split

After both APIs are complete, split each module:

- `Data.Text.Optic` (strict) / `Data.Text.Lazy.Optic` (lazy)
- `Data.ByteString.Optic` (strict) / `Data.ByteString.Lazy.Optic` (lazy)

Lazy modules add:
- `chunked :: Iso' LazyText [Text]` / `Iso' LazyByteString [ByteString]`
- `fromChunks`/`toChunks` based operations
- Lazy-specific fold/unfold variants

## Implementation approach

### Construction patterns

Each optic follows one of these construction patterns:

```haskell
-- Iso: pair of inverse functions
reversed = iso T.reverse T.reverse

-- Prism: matching + building
consed = prism (\(c, t) -> T.cons c t) (\t -> maybe (Left t) Right (T.uncons t))

-- Traversal0: lookup + update (via traversalVl0 or traversal0')
at i = traversal0' (\t -> if i < T.length t then Just (T.index t i) else Nothing)
                    (\t c -> ...) -- replace char at position i

-- Ixtraversal: via ixtraversalVl with incoming index
ixtraversed = ixtraversalVl $ \f k t ->
  T.pack <$> traverse (\(i, c) -> f (k <> Sum i) c) (zip [0..] (T.unpack t))

-- Fold0: extraction that may fail  
headed = fold0 (\t -> if T.null t then Nothing else Just (T.head t))

-- Cofold: building from seed
unfolding = cofoldVl $ \fab fs -> T.unfoldr ...

-- Colens/Grate: representable structure
justified w c = grateVl $ \f -> T.justifyLeft w c . T.pack . map (f ...) ...

-- Adjoint: SEC-style
filtered = adjoint T.filter

-- Cxoptics: via cxtraversalVl, cxsetter, cxfoldVl
cxtraversed = cxtraversalVl $ \fakb k fs -> ...
```

### Naming conventions

Follow the container optics pattern:
- Non-indexed optics that take a parameter: `at`, `split`, `prefixed`, etc.
- Indexed versions that drop the parameter: `ixat`, `ixtraversed`, etc.
- Coindexed duals: `cxtraversed`, `cxfolded`, `cxmapped`, `cxfiltered`
- Adjoint-level optics: `filtered`, `mapped` (these work with both `sets`/`ixsets`/`cxsets`)

### Index types

All positional indices use `Sum Int` (consistent with Sequence/List).

## Property testing approach

### Iso laws

```haskell
-- fromto: review o (view o s) == s
-- tofrom: view o (review o a) == a

prop_reversed_fromto s = Prop.fromto_iso reversed s
prop_consed_tofrom (c, t) = Prop.tofrom_prism consed (T.cons c t)
```

### Prism laws

```haskell
-- tofrom: preview o (review o a) == Just a
-- fromto: maybe s (review o) (preview o s) == s

prop_consed_tofrom (c, t) = Prop.tofrom_prism consed (c, t)
prop_consed_fromto t = Prop.fromto_prism consed t
prop_prefixed_tofrom pfx rest = Prop.tofrom_prism (prefixed pfx) rest
```

### Traversal laws

```haskell
-- identity: traverseOf o pure == pure
-- composition: fmap (traverseOf o f) . traverseOf o g == traverseOf o (Compose . fmap f . g) . Compose

prop_chars_id t = Prop.id_traversal chars t
prop_ixtraversed_id t = Prop.id_ixtraversal ixtraversed t
```

### Setter laws

```haskell
-- identity: sets o id == id
-- composition: sets o f . sets o g == sets o (f . g)

prop_mapped_id t = Prop.id_setter mapped t
prop_filtered_id t = Prop.id_adjoint filtered t
```

### Cofold / Colens laws

```haskell
-- Cofold identity: cofoldMapOf o id == copure
-- Colens const: cosets o (const . copure) == copure

prop_unfolding_id = ... -- test that cofold identity holds
prop_justified_const w c t = Prop.const_grate (justified w c) t
```

### Index threading

```haskell
-- Verify (.) accumulates indices for ixtraversed
prop_ixtraversed_indices t =
  let result = ixtoListOf ixtraversed t
  in fmap fst result == [Sum 0 .. Sum (T.length t - 1)]

-- Verify incoming index threads through
prop_ix_dot_ixtraversed =
  let result = ixtoListOf (ix (Sum 1) traversed . ixtraversed) ["ab", "cd"]
  in ...
```

### Round-trip properties for Prisms

```haskell
-- stripPrefix/(<>) round-trip
prop_prefixed_roundtrip pfx t =
  T.stripPrefix pfx (pfx <> t) == Just t

-- uncons/cons round-trip
prop_consed_roundtrip t =
  case T.uncons t of
    Nothing -> T.null t
    Just (c, rest) -> T.cons c rest == t
```

### Equivalence with upstream

```haskell
-- Each optic should agree with the upstream function
prop_mapped_eq_map f t = sets mapped f t == T.map f t
prop_folded_eq_foldl f z t = foldlOf' folded f z t == T.foldl' f z t
prop_filtered_eq_filter p t = sets (adjoint T.filter) p t == T.filter p t
prop_ixtraversed_eq_imap f t =
  over ixtraversed (\k c -> f (getSum k) c) t == T.pack (zipWith f [0..] (T.unpack t))
```

## Ordering

1. **Phase 1a**: Isos + Prisms (simplest, law-driven)
2. **Phase 1b**: Traversal0 / Fold0 (positional access)
3. **Phase 1c**: Indexed traversals/folds/setters
4. **Phase 1d**: Lenses on pairs + Adjoints
5. **Phase 2a**: Cofolds + Colenses
6. **Phase 2b**: Coindexed optics
7. **Phase 3**: Strict/Lazy split

Each phase is a separate commit.

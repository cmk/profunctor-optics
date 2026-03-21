# Sprint: Relens & Reprism

Integrate `Relens` (Costrong) and `Reprism` (Cochoice) optics from
`c28be9b:profunctor-optics-sort/src/Data/Profunctor/Optic/Import.hs` into the
core profunctor-optics library.

Source: `git show c28be9b:profunctor-optics-sort/src/Data/Profunctor/Optic/Import.hs`

---

## Known Issues ("hair")

### 1. `RelensRep` `Costrong` instance uses `undefined` (BLOCKER)
```haskell
instance Costrong (RelensRep a b) where
  unfirst (RelensRep baca bbc) = RelensRep (curry foo) (forget2 $ bbc . fst)
    where foo = uncurry baca . shuffle . B.second undefined . swap
          -- TODO: B.second bbc
```
The `B.second undefined` is a placeholder. The TODO suggests `B.second bbc`
but that hasn't been verified. This must be resolved before merging.

### 2. Code is in a flat file, needs splitting across modules
Currently everything lives in one `Import.hs`. Needs to be distributed:
- Type aliases → `Types.hs`
- Carrier profunctors (`RelensRep`, `ReprismRep`) → `Carrier.hs`
- `with*` destructors → `Carrier.hs`
- Relens constructors + stock optics → `Lens.hs`
- Reprism constructors + stock optics → `Prism.hs`
- `costrong` / `cochoice` combinators → `Combinator.hs` (keep `Costrong p` /
  `Cochoice p` signatures, note rank-2 specializations in haddocks)

### 3. Naming consistency to decide
The old code uses mixed conventions for indexed variants:
- `Rxlens` (coindexed relens) — `Rx` prefix, inconsistent with `Cx` used
  elsewhere for coindexed optics
- `Ixprism` (indexed prism) — this is new, prism doesn't currently have an
  indexed variant in core
- `rlens` / `rprism` — `r` prefix for indexed Relens/Reprism constructors
- `jprism` / `iprism` — `j` for "indexed matcher receives index", `i` for
  "matcher returns index" — convention needs documenting

---

## Sprint 1: Core Relens & Reprism (no indexed variants)

### S1.1 Add types to `Types.hs`
- [ ] Add `Relens s t a b = forall p. Costrong p => Optic p s t a b`
- [ ] Add `Relens' s a = Relens s s a a`
- [ ] Add `Reprism s t a b = forall p. Cochoice p => Optic p s t a b`
- [ ] Add `Reprism' s a = Reprism s s a a`
- [ ] Add to export list under new `-- * Relens` and `-- * Reprism` sections
- [ ] Add haddock with LaTeX characterization (like existing optic types)
- [ ] Update `Re` docs: `re :: Lens -> Relens`, `re :: Prism -> Reprism`
- [ ] Clean up TODO at line 390 — document what `re` can reverse and what it
  can't, remove mention of `Closed`/`Representable`/`Corepresentable`

### S1.2 Add carriers to `Carrier.hs`
- [ ] Add `RelensRep a b s t` data type with `Profunctor` instance
- [ ] **Fix** `Costrong (RelensRep a b)` instance — resolve the `undefined`
- [ ] Add `ARelens s t a b` and `ARelens' s a` type aliases
- [ ] Add `withRelens :: ARelens s t a b -> ((b -> s -> a) -> (b -> t) -> r) -> r`
- [ ] Add `ReprismRep a b s t` data type with `Profunctor`, `Functor` instances
- [ ] Add `Cochoice (ReprismRep a b)` instance (this one looks correct in source)
- [ ] Add `AReprism s t a b` and `AReprism' s a` type aliases
- [ ] Add `withReprism :: AReprism s t a b -> ((s -> a) -> (b -> Either a t) -> r) -> r`
- [ ] Add to export list

### S1.3 Add constructors & stock optics to `Lens.hs`
- [ ] `relens :: (b -> s -> a) -> (b -> t) -> Relens s t a b`
- [ ] `relensVl :: (forall f. Functor f => (t -> f s) -> b -> f a) -> Relens s t a b`
- [ ] `rematching :: ((c, s) -> a) -> (b -> (c, t)) -> Relens s t a b`
- [ ] `cloneRelens :: ARelens s t a b -> Relens s t a b`
- [ ] `refirst :: Relens a b (a, c) (b, c)` (= `unfirst`)
- [ ] `resecond :: Relens a b (c, a) (c, b)` (= `unsecond`)
- [ ] Add `Costrong(..)` to re-exports from `Lens.hs`
- [ ] Add haddocks for all functions
- [ ] Add to export list under new `-- * Relens` section

### S1.4 Add constructors & stock optics to `Prism.hs`
- [ ] `reprism :: (s -> a) -> (b -> Either a t) -> Reprism s t a b`
- [ ] `reprism' :: (s -> a) -> (a -> Maybe s) -> Reprism' s a`
- [ ] `rehandling :: (Either c s -> a) -> (b -> Either c t) -> Reprism s t a b`
- [ ] `cloneReprism :: AReprism s t a b -> Reprism s t a b`
- [ ] `releft :: Reprism a b (Either a c) (Either b c)` (= `unleft`)
- [ ] `reright :: Reprism a b (Either c a) (Either c b)` (= `unright`)
- [ ] Add `Cochoice(..)` to re-exports from `Prism.hs`
- [ ] Add haddocks for all functions
- [ ] Add to export list under new `-- * Reprism` section

### S1.5 Add combinators to `Combinator.hs`
- [ ] `costrong :: Costrong p => ((t, s) -> a) -> p a t -> p s t`
  Haddock should note the rank-2 specialization:
  @costrong :: ((t, s) -> a) -> 'Relens' s t a t@
- [ ] `cochoice :: Cochoice p => (b -> Either s t) -> p s b -> p s t`
  Haddock should note the rank-2 specialization:
  @cochoice :: (b -> Either s t) -> 'Reprism' s t s b@
- [ ] Add haddocks

### S1.6 Re-export from `Data.Profunctor.Optic`
- [ ] Add `Relens`, `Relens'`, `Reprism`, `Reprism'` to top-level re-exports
- [ ] Add all new constructors/destructors/stock optics

### S1.7 Tests & verification
- [ ] Verify `re (lens sa sbt)` gives a `Relens` — types check
- [ ] Verify `re (prism sta bt)` gives a `Reprism` — types check
- [ ] Verify `re . re ≡ id` round-trips for both
- [ ] Add property tests to `Property.hs`:
  - `relens` laws (dual of lens laws)
  - `reprism` laws (dual of prism laws)
- [ ] Verify `refirst`, `resecond`, `releft`, `reright` against `re first`,
  `re second`, `re left`, `re right`

---

## Sprint 2: Indexed Relens & Reprism + Ixprism

### S2.1 Indexed types to `Types.hs`
- [ ] `Rxlens r s t a b = forall p. Costrong p => Ixoptic p r s t a b`
  - Decide: should this use `Cx` prefix? (`Cxrelens`?)
- [ ] `Ixprism i s t a b = forall p. Choice p => Ixoptic p i s t a b`
- [ ] `Rxprism r s t a b = forall p. Cochoice p => Ixoptic p r s t a b`
  - Same prefix question
- [ ] Simple variants for all

### S2.2 Indexed constructors to `Lens.hs`
- [ ] `rlens :: (b -> s -> (r, a)) -> (b -> t) -> Rxlens r s t a b`
- [ ] `rlensVl :: (forall f. Functor f => (t -> f s) -> b -> f (r, a)) -> Rxlens r s t a b`
- [ ] `rfirst :: Rxlens r a b (a, c) (b, c)`
- [ ] `rsecond :: Rxlens r a b (c, a) (c, b)`

### S2.3 Indexed constructors to `Prism.hs`
- [ ] `jprism :: (i -> s -> Either t a) -> (b -> t) -> Ixprism i s t a b`
- [ ] `iprism :: (s -> Either t (i, a)) -> (b -> t) -> Ixprism i s t a b`
- [ ] `iprism' :: (s -> Maybe (i, a)) -> (a -> s) -> Ixprism' i s a`
- [ ] `jprism' :: (i -> s -> Maybe a) -> (a -> s) -> Ixprism' i s a`
- [ ] `rprism :: Monoid r => (r -> s -> a) -> (b -> Either a t) -> Rxprism r s t a b`
- [ ] `rprism' :: Monoid r => (r -> s -> a) -> (a -> Maybe s) -> Rxprism' r s a`

### S2.4 Naming audit
- [ ] Decide: `Rx` vs `Cx` prefix for coindexed Relens/Reprism
- [ ] Decide: `j` vs `i` prefix convention — document the difference
  (`j` = index is input to matcher, `i` = index is output of matcher)
- [ ] Apply rename from B1 (`Rxsetter` → `Cxsetter`) if decided

---

## Diagram: Where Relens & Reprism Sit

```
                    Equality
                       |
                      Iso
                    /     \
                Lens       Prism
               / |  \       |  \
        Colens   |  Relens  | Reprism
           |     |     |    |     |
           .   View  Review .     .
```

Relens and Reprism are siblings of Lens and Prism respectively, reached
via `Re`-reversal rather than the `Closed`-based co-dual:

- `Lens`   = `Strong p`   →  `re` →  `Relens`  = `Costrong p`
- `Prism`  = `Choice p`   →  `re` →  `Reprism` = `Cochoice p`
- `Lens`   = `Strong p`   →  co  →  `Colens`  = `Closed p`

A `Relens` is simultaneously a `View` and a `Review` (it can both
`view` in one direction and `review` in the other), but it is not an
`Iso` because the round-trip laws don't hold.

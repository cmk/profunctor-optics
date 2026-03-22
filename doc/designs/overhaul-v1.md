# profunctor-optics Overhaul Plan — targeting v1.0.0

Improvement areas identified by comparing profunctor-optics against lens and
optics-core, and auditing the current codebase. Organized by category with
rough priority (P1 = blocking / correctness, P2 = important for completeness,
P3 = nice to have).

Design constraint: **zero new type classes**. The entire library is built on
existing profunctor classes (`Strong`, `Choice`, `Closed`, `Representable`,
`Corepresentable`, etc.) and their interactions. This is a deliberate
category-theoretic design choice, not an omission.

Note on duality: The library has two distinct notions of "reversal":
1. **`Re`-reversal**: swaps `Strong ↔ Costrong`, `Choice ↔ Cochoice`. This
   gives `ReversedLens` (Costrong) and `ReversedPrism` (Cochoice) in
   optics-core's terminology.
2. **Categorical co-dual**: replaces `Strong` with `Closed`, giving a
   fundamentally different and more useful optic family. This is what
   `Colens`, `Cotraversal`, `Cofold`, etc. are. `Closed` won the name
   `Colens` over `Costrong` because it is substantially more useful (grates,
   zipping, distributive traversals).

Status key: `[ ]` todo, `[~]` in progress, `[x]` done, `[-]` won't do

---

## A. Carrier Completeness

### A1. `Re` — assess current TODO (P2)
- [ ] Review the TODO at `Types.hs` ~line 390 mentioning `Closed`,
  `Representable`, `Corepresentable` instances for `Re`
- [ ] Determine which (if any) of these are actually achievable and useful.
  `Re` already handles `Strong ↔ Costrong` and `Choice ↔ Cochoice`.
  `Closed` has no standard dual class, so a `Closed (Re p)` instance may
  not be meaningful. If the TODO is a dead end, remove it.
- [ ] Document what `re` can and cannot reverse, and why.

### A2. `CoaffineRep` missing `Corepresentable` (P2)
- [ ] Implement `Corepresentable` instance for `CoaffineRep`
- [ ] Implement `Coapplicative` for the `Corep` of `CoaffineRep`
- **Location**: `Carrier.hs` ~line 540
- **Why**: Breaks symmetry with `AffineRep` (which is fully `Representable`).
  Prevents `withCoaffine` from working in all expected contexts.

### A3. `Coindex` missing `Coapply` (P3)
- [ ] Implement `Coapply (Coindex a b)` instance
- **Location**: `Carrier.hs` ~line 853
- **Why**: Blocks grate/colens ops with `cotraverse1`.

### A4. `Cofold` constraint — verify correctness (P2)
- [ ] Audit whether `Cofold` using `Affine p` (= `Strong p, Choice p`) is
  correct, or whether it should use `Coaffine p` (= `Closed p, Choice p`)
- [ ] Same audit for `Cofold1`
- [ ] Check downstream: `cofoldVl`, `cofolding`, `cofolds`, `cofoldsa`
- **Location**: `Types.hs`
- **Context**: Initially flagged as a likely bug, but given the deliberate
  design of the co-hierarchy this needs careful analysis. A `Cofold` that
  requires `Strong` (lens-side) instead of `Closed` (grate-side) might be
  intentional if the fold direction demands it, but it should be documented
  either way.

---

## B. Naming & Consistency

### B1. Rename `Rxsetter` to `Cxsetter` (P2)
- [ ] Rename type alias
- [ ] Rename carrier `ARxsetter` to `ACxsetter`
- [ ] Update all uses in Setter.hs, Carrier.hs
- **Why**: Every other coindexed type uses the `Cx` prefix.

### B2. Add `AffineTraversal` / `AffineFold` aliases (P2)
- [ ] `type AffineTraversal s t a b = Traversal0 s t a b`
- [ ] `type AffineFold s a = Fold0 s a`
- [ ] Export from Types module
- **Why**: Rest of the ecosystem uses these names. Helps discoverability
  without breaking existing code.

### B3. Consider renaming fold/traversal operations (P3)
Current names vs ecosystem convention:
| Current | lens / optics-core | Decision |
|---|---|---|
| `lists` | `toListOf` | [ ] |
| `folds` | `foldMapOf` | [ ] |
| `foldsr` | `foldrOf` | [ ] |
| `foldsl` | `foldlOf` | [ ] |
| `foldsl'` | `foldlOf'` | [ ] |
| `traverses` | `traverseOf` | [ ] |
| `sequences` | `sequenceOf` | [ ] |
| `fmapped` | `mapped` | [ ] |
| `equaled` | `equality` | [ ] |
| `matches` | `matching` | [ ] |
| `invert` | `from` (lens) / `re` (optics-core) | [ ] |
- **Why**: Major version bump with no users = opportunity to align. Reduces
  friction for anyone familiar with lens/optics.

### B4. `prism` / `prism'` argument order (P3)
- [ ] Decide: keep `(match, build)` or align with lens/optics-core `(build, match)`
- Currently documented with a note. Either way, make it a deliberate choice.

### B5. Operator alignment (P3)
| Current | lens / optics-core | Notes |
|---|---|---|
| `(..~)` (over) | `(%~)` | You use `(%~)` for indexed over |
| `(.^)` (review) | `(#)` | You use `(#)` for cx composition |
| `(^%%)` (ix toList) | (none) | Consider dropping |
- [ ] Decide on operator assignments
- **Why**: `(%~)` for over is deeply ingrained muscle memory in the Haskell
  ecosystem.

---

## C. Missing Functionality

Note: Items C2, C3, C5, C6 would introduce new type classes, which conflicts
with the library's zero-type-class design constraint. They are included for
discussion but may belong in a separate companion package, or may be achievable
via standalone functions instead of classes.

### C1. Fold query functions (P2)
- [ ] `has :: AFold0 a s a -> s -> Bool`
- [ ] `hasn't :: AFold0 a s a -> s -> Bool`
- [ ] `anyOf :: AFold r s a -> (a -> Bool) -> s -> Bool`
- [ ] `allOf :: AFold r s a -> (a -> Bool) -> s -> Bool`
- [ ] `noneOf :: AFold r s a -> (a -> Bool) -> s -> Bool`
- [ ] `lengthOf :: AFold r s a -> s -> Int`
- [ ] `sumOf :: Num a => AFold r s a -> s -> a`
- [ ] `productOf :: Num a => AFold r s a -> s -> a`
- [ ] `maximumOf :: Ord a => AFold r s a -> s -> Maybe a`
- [ ] `minimumOf :: Ord a => AFold r s a -> s -> Maybe a`
- [ ] `findOf :: AFold r s a -> (a -> Bool) -> s -> Maybe a`
- [ ] `elemOf :: Eq a => AFold r s a -> a -> s -> Bool`
- [ ] `headOf :: AFold r s a -> s -> Maybe a`  (non-monadic `firstOf`)
- [ ] `lastOf :: AFold r s a -> s -> Maybe a`
- **Why**: The primitives (`foldsr`, `foldsl'`) exist but not the convenient
  wrappers. These are the most-used fold operations in practice. No new
  classes needed.

### C2. Container access: `At` / `Ixed` style (P3)
- [ ] Decide whether to provide as type classes (breaks zero-class constraint)
  or as standalone functions per container type
- [ ] If standalone: `mapAt`, `mapIx`, `seqIx`, `intMapAt`, etc.
- [ ] If classes: consider putting in a companion package (e.g.
  `profunctor-optics-containers` or similar)

### C3. `Cons` / `Snoc` style (P3)
- [ ] Same class-vs-standalone decision as C2
- [ ] `_head`, `_tail`, `_last`, `_init` as standalone functions per type
  would work without classes

### C4. `partsOf` / `singular` (P3)
- [ ] `partsOf :: ATraversal f s t a b -> Lens' s [a]`
- [ ] `singular :: ATraversal f s t a b -> Traversal0 s t a b`
- **Why**: Power tools for traversal manipulation. No new classes needed.

### C5. `Each` / `AsEmpty` style (P3)
- [ ] Same class-vs-standalone decision as C2
- [ ] `_Empty` as standalone prisms per type would work without classes

### C6. Recursive traversals (P3)
- [ ] `rewriteOf`, `transformOf` (just setter operations, no class needed)
- [ ] `universeOf`, `cosmosOf`, `paraOf` (just fold operations, no class needed)
- [ ] `Plated`-style class: conflicts with zero-class constraint, consider
  companion package or omit

### C7. Pure `view` variant (P3)
- [ ] Consider adding a pure `view :: AView a s a -> s -> a` alongside the
  current MonadReader-generalized version
- [ ] Or rename current to `gview` and make `view` pure
- **Why**: Simpler type signature for the common case.

---

## D. Code Quality

### D1. Document the ~85 undocumented functions (P2)
Priority modules:
- [ ] `Combinator.hs` — `(%)`, `(#)`, `reix`, `recx`, `represent`, etc.
- [ ] `Fold.hs` — indexed fold operations
- [ ] `Traversal.hs` — indexed traversal operations, `ix`, `noix`
- [ ] `Setter.hs` — indexed setter operations
- [ ] `View.hs` — indexed view/review operations
- [ ] `Carrier.hs` — carrier types and `with*` functions

### D2. Re-enable doctest suite (P2)
- [ ] Add doctests to `Sort.hs` (the blocker)
- [ ] Uncomment doctest stanza in cabal file
- [ ] Verify all existing doctests still pass

### D3. Clean up dead code (P3)
- [ ] Remove duplicate `import qualified Control.Category as C` in `Carrier.hs`
- [ ] Resolve commented-out code blocks in `Combinator.hs`:
  - `cxjoin`, `cxreturn`, `cxunit`, `cxfirst`, `cxpastro`
  - Alternative `(%)` / `(#)` implementations
  - `pushl` / `pushr`
- [ ] Either implement or remove `Coindex` `Coapply` stub

### D4. Property tests for new optics (P3)
- [ ] Add property tests for `Traversal0` laws
- [ ] Add property tests for `Colens` laws
- [ ] Add property tests for `Cotraversal` laws
- [ ] Extend existing tests for container optics

---

## E. Dependency / Build Considerations

### E1. GHC version range (P3)
- [ ] Decide minimum GHC: currently `base >= 4.16` (GHC 9.2) but only tested
  with 9.6.7. Consider testing with 9.8 / 9.10 as well.

### E2. `coapplicative` dependency (P3)
- [ ] Verify `coapplicative` is published and accessible. It appears to be an
  in-house package. If it's not on Hackage, document how to obtain it.

### E3. Evaluate profunctors dependency (P3)
- [ ] Check if local profunctors at `/Users/cmk/Documents/Code/haskell/profunctors`
  has changes that profunctor-optics should track or depend on.

---

## Suggested Implementation Order

Phase 1 — Audit & fix (can be done in parallel):
  - A1 (Re TODO — assess and document or remove)
  - A2 (CoaffineRep Corepresentable)
  - A4 (Cofold constraint audit)

Phase 2 — Core API improvements:
  - B1 (Rxsetter rename)
  - B2 (AffineTraversal/AffineFold aliases)
  - C1 (fold query functions)
  - C7 (pure view)

Phase 3 — Ecosystem alignment (after deciding on naming):
  - B3 (rename fold/traversal ops)
  - B4 (prism argument order)
  - B5 (operator alignment)

Phase 4 — Power features:
  - C4 (partsOf/singular)
  - C6 (recursive traversals — standalone functions only)

Phase 5 — Container infrastructure (decision needed on class constraint):
  - C2 (At/Ixed — standalone or companion package)
  - C3 (Cons/Snoc — standalone or companion package)
  - C5 (Each/AsEmpty — standalone or companion package)

Phase 6 — Polish:
  - D1-D4 (docs, tests, cleanup)

---

## F. Release Readiness

### F1. Stale Moore/Mealy exports in `Types.hs` (P1)
- [ ] `Types.hs` exports Moore/Mealy types that were moved to
  `profunctor-optics-folds`. Either remove the stale exports or add
  re-exports from the folds package.
- **Why**: Blocks clean compilation or gives users broken imports.

### F2. Stale doc references across modules (P1)
- [ ] ~25 doc references to `Data.Profunctor.Optic.Property` across Fold,
  Setter, Iso, Lens, Traversal, Prism modules — update or remove
- [ ] 1 doc reference to removed `Data.Profunctor.Optic.Moore` in
  `Traversal.hs` — remove
- **Why**: Broken Haddock links in published docs.

### F3. Doctest suite disabled (P2)
- [ ] Add doctests to `Sort.hs` (the stated blocker in cabal file)
- [ ] Uncomment doctest stanza in cabal file
- [ ] Verify all existing doctests still pass
- **Note**: Overlaps with D2. Listed here for release-gate visibility.

### F4. ChangeLog.md (P1)
- [ ] Replace placeholder template with real release notes for 0.0.3 → 1.0.0
- [ ] Document all breaking API changes (renames, removed modules, moved
  types)
- [ ] Document new functionality added

### F5. README accuracy (P2)
- [ ] Core package README claims features no longer in core (indexed
  variants, property predicates, Moore/Mealy). Update to reflect current
  state.
- [ ] Root monorepo README is just "see individual packages" — consider a
  brief overview of the ecosystem.

### F6. Copyright year (P3)
- [ ] Update copyright from 2019 to 2019-2026 in all cabal files
- [ ] Update LICENSE files if applicable

### F7. Unused import warnings (P2)
- [ ] `Types.hs:108` — redundant `Data.Functor.Apply` import
- [ ] `Carrier.hs:135` — redundant `Control.Category` import
- [ ] `Carrier.hs:137` — redundant `Data.Profunctor.Types` re-export
- [ ] `Carrier.hs:140` — redundant `Data.Monoid` import
- [ ] `Carrier.hs:149` — redundant qualified `Control.Category` import
- [ ] `Prism.hs:43` — redundant `Control.Monad` import
- [ ] `Prism.hs:46` — redundant `(++)` import from `Data.List`
- **Why**: Clean `-Wall` build for release.

### F8. CI coverage (P2)
- [ ] Restore GHC 9.4 and 9.8 test matrix (currently only 9.6)
- [ ] Consider adding GHC 9.10 if deps support it
- [ ] Re-enable benchmarks in CI (currently `False`)

### F9. Support package version coordination (P3)
- [ ] All support packages are at 0.0.1 — decide whether they get bumped
  in lockstep with core or independently
- [ ] Ensure support package dependency bounds on `profunctor-optics` are
  compatible with the new version

### F10. API rename completion (P1)
- [ ] The current branch (`truncate`) has commits "Refactor API names"
  1–5/n — determine if the rename series is complete
- [ ] If not, finish remaining renames before cutting the release
- [ ] Ensure all renames are reflected in the changelog

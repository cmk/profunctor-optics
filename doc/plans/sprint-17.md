# Sprint 17 — Types.hs cleanup, property tests, and API gaps

## Scope

Land the Types.hs overhaul (LaTeX equations, Cofold constraint fix,
Re documentation), fill gaps in Property.hs and Test/Carrier.hs, and
begin filling the missing fold query functions from overhaul plan C1.

## Rationale

The v1.0.0 release needs:
1. Correct constraints — the Cofold/Cofold1 constraint fix (Affine →
   Coaffine, Choice → Closed) is landed but untested.
2. Property coverage — half the optic families have no property
   predicates or hedgehog tests.
3. API completeness — the fold query functions (`has`, `hasn't`,
   `anyOf`, `allOf`, etc.) are the most-requested missing pieces
   and require no new type classes.

## Completed (this session)

| ID     | Target | Description | Status |
|--------|--------|-------------|--------|
| S17.0a | Types.hs | LaTeX equations for all optic types (primal, indexed, coindexed) | done |
| S17.0b | Types.hs | Named doc chunks (`-- $name`) so equations render above types | done |
| S17.0c | Types.hs | Fix Cofold constraint: `Affine` → `Coaffine` | done |
| S17.0d | Types.hs | Fix Cofold1 constraint: `Choice` → `Closed` | done |
| S17.0e | Types.hs | Move Ix/Ix' above Ixoptic, Cx/Cx' above Cxoptic | done |
| S17.0f | Types.hs | Document Re limitations (no Closed/Representable dual) | done |
| S17.0g | Types.hs | Remove duplicate DeriveGeneric pragma, fix `-- * Iso,` comma | done |
| S17.0h | all modules | Reorder implementations to match export lists | done |
| S17.0i | overhaul-v1.md | Append release readiness section (F1–F10) | done |

## Stories

| ID     | Target | Description |
|--------|--------|-------------|
| S17.1  | Property.hs | Uncomment and fix `compose_cotraversal` |
| S17.2  | Property.hs | Add Cosetter laws: `id_cosetter`, `compose_cosetter` |
| S17.3  | Property.hs | Add Cofold property predicates |
| S17.4  | Property.hs | Add Traversal1 identity/composition predicates |
| S17.5  | Property.hs | Add indexed optic law predicates (Ixlens, Ixtraversal) |
| S17.6  | Test/Carrier.hs | Hedgehog tests for Traversal (identity, composition) |
| S17.7  | Test/Carrier.hs | Hedgehog tests for Cofold/Cofold1 (validates constraint fix) |
| S17.8  | Test/Carrier.hs | Hedgehog tests for Cosetter |
| S17.9  | Test/Carrier.hs | Hedgehog tests for indexed optics |
| S17.10 | Fold.hs | Fold query functions: `has`, `hasn't`, `anyOf`, `allOf`, `noneOf` | already implemented |
| S17.11 | Fold.hs | Fold query functions: `lengthOf`, `sumOf`, `productOf` | already implemented |
| S17.12 | Fold.hs | Fold query functions: `maximumOf`, `minimumOf`, `findOf`, `elemOf` | already implemented |
| S17.13 | Fold.hs | Fold query functions: `headOf`, `lastOf` | already implemented |
| S17.14 | Types.hs | Remove dead CPP guards (`MIN_VERSION_profunctors(5,4,0)` etc.) |
| S17.15 | Types.hs | Clean up unused import (`Data.Functor.Apply`) |
| S17.16 | Carrier.hs | Implement `Corepresentable` for `Cotraversal0Rep` (overhaul A2) |
| S17.17 | Carrier.hs | Implement `Coapply` for `Coindex` (overhaul A3) |
| S17.18 | Carrier.hs | Rename rank-2 `with*` to `with*Vl`, add missing `with*Vl` operators |
| S17.19 | Fold.hs | Add missing Fold constructors and optics |
| S17.20 | Lens.hs | Add missing Rxlens constructors (`rxlens`, `rxlensVl`, `cloneRxlens`) |
| S17.21 | Lens.hs | Add missing `cloneRelensVl`, `cloneIxlens`, `cloneCxlens` |
| S17.22 | Traversal.hs | Add missing clone functions for all traversal families |
| S17.23 | Traversal.hs | Add Cotraversal0 constructors (only type is exported, no constructors) |
| S17.24 | Traversal.hs | Add missing indexed/coindexed operator variants |
| S17.25 | Prism.hs, Carrier.hs, Property.hs, Test/ | Ixprism/Rxprism: constructors, carriers, optics, operators, properties |
| S17.26 | View.hs | Add missing indexed/coindexed View/Review API |
| S17.27 | Setter.hs | Add missing Setter constructors, clones, and indexed MTL operators |
| S17.28 | Types.hs, View.hs, Fold.hs, Carrier.hs, all | Rename Review→Coview, add true Review (Costrong+CoercingL) |
| S17.29 | Infix.hs | Implement `(^##)` — coindexed cofold to list |

## S17.1 — Uncomment compose_cotraversal

The predicate exists but is commented out. Likely needs `Coapplicative`
instances for the test functors. Check whether `Identity` and `Compose`
have the right instances via `coapplicative`.

## S17.2 — Cosetter laws

Dual of Setter. The laws are:

```haskell
-- | @coset o id ≡ id@
id_cosetter :: Eq s => Cosetter' s a -> s -> Bool

-- | @coset o f . coset o g ≡ coset o (f . g)@
compose_cosetter :: Eq s => Cosetter' s a -> (a -> a) -> (a -> a) -> s -> Bool
```

These go through the `Costar` carrier. Need `withCosetter` or
`cloneCosetterVl` — check what's available in Carrier.hs.

## S17.3 — Cofold property predicates

Now that Cofold uses `Coaffine` (Closed + Choice), we need tests
that exercise the `Closed` constraint path. Predicates:

```haskell
-- | @cofoldMapOf o id ≡ id@
id_cofold :: Eq t => Cofold t b -> t -> Bool

-- | Composition through cofoldMapOf
compose_cofold :: Eq t => Cofold t b -> (b -> b) -> (b -> b) -> t -> Bool
```

Test with `cofolded` on distributive functors (e.g. `Identity`,
`((->) r)`).

## S17.4 — Traversal1 predicates

```haskell
id_traversal1 -- already exists in Property.hs
-- add:
pure_traversal1 :: Eq (f s) => Apply f => ATraversal1' f s a -> s -> Bool
```

## S17.5 — Indexed optic law predicates

The indexed variants should satisfy the same structural laws as
their non-indexed counterparts, but with index threading:

```haskell
-- | Indexed lens: get-set, set-get, set-set
tofrom_ixlens :: Eq s => Ixlens' k s a -> s -> Bool
fromto_ixlens :: Eq a => Eq k => Ixlens' k s a -> s -> a -> Bool
idempotent_ixlens :: Eq s => Ixlens' k s a -> s -> a -> a -> Bool

-- | Indexed traversal: identity, composition
id_ixtraversal :: Eq s => Ixtraversal' k s a -> s -> Bool
```

## S17.6–S17.9 — Hedgehog tests

### S17.6 — Traversal tests

```haskell
prop_traversal_id :: Property        -- runIdentity . traverseOf traversed Identity ≡ id
prop_traversal_compose :: Property   -- fmap/Compose law
```

### S17.7 — Cofold tests (validates constraint fix)

```haskell
prop_cofold_id :: Property           -- cofoldMapOf cofolded id ≡ id (on Identity)
prop_cofold_cofolding :: Property    -- cofolding round-trip
```

These are the key tests — if the Closed constraint is wrong, the
Costar carrier won't have the right instances and these will fail
at the type level.

### S17.8 — Cosetter tests

```haskell
prop_cosetter_id :: Property         -- over o id ≡ id (through Costar)
prop_cosetter_compose :: Property    -- over o f . over o g ≡ over o (f . g)
```

### S17.9 — Indexed optic tests

```haskell
prop_ixlens_tofrom :: Property       -- ixlens get-set
prop_ixlens_fromto :: Property       -- ixlens set-get
prop_ixtraversal_id :: Property      -- identity through ixtraversed
prop_ixfold_foldmap :: Property      -- ixfoldMapOf consistency
```

## S17.10–S17.13 — Fold query functions

These are the most-used fold operations in practice (overhaul plan C1).
No new type classes needed — they're all wrappers around `foldMapOf`,
`foldrOf`, `foldlOf'`, and `preview`.

### S17.10 — Boolean queries

```haskell
has      :: AFold0 a s a -> s -> Bool
hasn't   :: AFold0 a s a -> s -> Bool
anyOf    :: AFold r s a -> (a -> Bool) -> s -> Bool
allOf    :: AFold r s a -> (a -> Bool) -> s -> Bool
noneOf   :: AFold r s a -> (a -> Bool) -> s -> Bool
```

### S17.11 — Numeric aggregations

```haskell
lengthOf  :: AFold (Sum Int) s a -> s -> Int
sumOf     :: Num a => AFold (Sum a) s a -> s -> a
productOf :: Num a => AFold (Product a) s a -> s -> a
```

### S17.12 — Search and extrema

```haskell
maximumOf :: Ord a => AFold (Endo (Maybe a)) s a -> s -> Maybe a
minimumOf :: Ord a => AFold (Endo (Maybe a)) s a -> s -> Maybe a
findOf    :: AFold (Endo (Maybe a)) s a -> (a -> Bool) -> s -> Maybe a
elemOf    :: Eq a => AFold Any s a -> a -> s -> Bool
```

### S17.13 — Head and last

```haskell
headOf :: AFold (First a) s a -> s -> Maybe a
lastOf :: AFold (Last a) s a -> s -> Maybe a
```

These overlap with `preview` / `foldOf0` but provide non-monadic
alternatives with clearer intent.

## S17.14 — Dead CPP guards (done)

All three `MIN_VERSION_profunctors` guards were dead (resolved 5.6.3).
Removed CPP entirely: stripped `CPP` pragma, `#ifndef` guard, and three
conditional blocks. Removed dead orphans `Contravariant (Star f a)` and
`Cochoice (Forget r)`, unwrapped always-true `Choice (Costar f)`.

## S17.15 — Unused import (done)

`Data.Functor.Apply (Apply(..))` removed — re-exported from Import.
Also removed 6 unused pragmas: `ExistentialQuantification`,
`DeriveGeneric`, `DeriveDataTypeable`, `PolyKinds`, `TupleSections`,
`DeriveFunctor`.

## S17.16 — Implement `Corepresentable` for `CoaffineRep`

Overhaul plan A2. Requires defining `Corep CoaffineRep` and implementing
`Coapplicative` for it. Breaks symmetry with `AffineRep` (which is fully
`Representable`) if missing.

## S17.17 — Implement `Coapply` for `Coindex`

Overhaul plan A3. Blocks grate/colens ops with `cotraverse1`.

## S17.18 — Rename rank-2 `with*` to `with*Vl`, add missing operators

Two `with*` functions use rank-2 types (VL formulation) but aren't
named accordingly:

| Current | Rename to | Reason |
|---|---|---|
| `withCotraversal` | `withCotraversalVl` | Returns `forall f. Coapplicative f => ...` |
| `withCxtraversal` | `withCxtraversalVl` | Returns `forall f. Coapplicative f => ...` |

Missing `with*Vl` operators to add (all rank-2, extract VL form):

```haskell
withTraversalVl    :: ATraversal f s t a b -> ((forall g. Applicative g => (a -> g b) -> s -> g t) -> r) -> r
withTraversal1Vl   :: ATraversal1 f s t a b -> ((forall g. Apply g => (a -> g b) -> s -> g t) -> r) -> r
withCotraversal1Vl :: ACotraversal1 f s t a b -> ((forall g. Coapply g => (g a -> b) -> g s -> t) -> r) -> r
withCofoldVl       :: ACofold r t b -> ((forall g. Coapplicative g => (g a -> b) -> g t -> t) -> r) -> r
withCofold1Vl      :: ACofold1 r t b -> ((forall g. Coapply g => (g a -> b) -> g t -> t) -> r) -> r
```

Note: Traversal/Cotraversal families don't have a separate "rep"
form — the VL form IS the natural extraction. Lens/Prism/etc.
extract concrete getter/setter pairs, so no `Vl` suffix needed.

## S17.19 — Missing Fold constructors and optics

**Missing indexed-direct constructors:**

```haskell
-- Fold indexed-direct (parallel to fold_)
ixfold_   :: Foldable f => (s -> f (k, a)) -> Ixfold k s a

-- Fold indexed-from-functor (parallel to folding)
ixfolding :: Traversable f => (s -> (k, a)) -> Ixfold k (f s) a

-- Fold0 indexed-concrete (parallel to afold0)
aixfold0  :: ((k -> a -> Maybe r) -> s -> Maybe r) -> AIxfold0 r k s a

-- Fold1 indexed-direct (parallel to fold1_)
ixfold1_   :: Foldable1 f => (s -> f (k, a)) -> Ixfold1 k s a

-- Fold1 indexed-from-functor (parallel to folding1)
ixfolding1 :: Traversable1 f => (s -> (k, a)) -> Ixfold1 k (f s) a
```

**Missing concrete constructors:**

```haskell
-- Fold1 concrete (parallel to afold/aixfold)
afold1   :: ((a -> r) -> s -> r) -> ATraversal1 (Const r) s t a b
aixfold1 :: ((k -> a -> r) -> s -> r) -> AIxtraversal1 (Const r) k s t a b
```

**Missing coindexed VL constructors:**

```haskell
cxfoldVl  :: (forall f. Coapplicative f => (f a -> k -> b) -> f s -> t) -> Cxfold k t b
acofold1  :: ((r -> b) -> r -> t) -> ACofold1 r t b
cxfoldVl1 :: (forall f. Coapply f => (f a -> k -> b) -> f s -> t) -> Cxfold1 k t b
```

**Missing optics:**

```haskell
cofolded1 :: Distributive1 g => Cofold1 (g b) b
```

## S17.20 — Rxlens constructors

Rxlens has no constructors at all. The full set to add:

```haskell
rxlens   :: (b -> (k , s) -> a) -> (b -> t) -> Rxlens k s t a b
rxlensVl :: (forall f. Functor f => (k -> t -> f s) -> b -> f a) -> Rxlens k s t a b
cloneRxlens :: ARxlens k s t a b -> Rxlens k s t a b
```

These are the Re-duals of Ixlens, analogous to how Relens is the
Re-dual of Lens.

## S17.21 — Missing clone/VL functions in Lens.hs

```haskell
cloneRelensVl :: ARelens s t a b -> (forall f. Functor f => (t -> f s) -> b -> f a)
cloneIxlens   :: AIxlens k s t a b -> Ixlens k s t a b
cloneIxlensVl :: AIxlens k s t a b -> (forall f. Functor f => (k -> a -> f b) -> s -> f t)
cloneCxlens   :: ACxlens k s t a b -> Cxlens k s t a b
cloneCxlensVl :: ACxlens k s t a b -> (forall f. Functor f => (f a -> k -> b) -> f s -> t)
```

## S17.22 — Missing clone functions in Traversal.hs

No `clone*` functions exist in Traversal.hs. Add for each family:

```haskell
-- Traversal
cloneTraversal   :: ATraversal f s t a b -> Traversal s t a b  -- tricky: needs to abstract over f
cloneTraversalVl :: ATraversal f s t a b -> (forall g. Applicative g => (a -> g b) -> s -> g t)

-- Traversal0
cloneTraversal0 :: ATraversal0 s t a b -> Traversal0 s t a b
-- (goes through withTraversal0 . traversal0)

-- Traversal1
cloneTraversal1Vl :: ATraversal1 f s t a b -> (forall g. Apply g => (a -> g b) -> s -> g t)

-- Cotraversal
cloneCotraversal   :: ACotraversal f s t a b -> Cotraversal s t a b
cloneCotraversalVl :: ACotraversal f s t a b -> (forall g. Coapplicative g => (g a -> b) -> g s -> t)

-- Cotraversal1
cloneCotraversal1Vl :: ACotraversal1 f s t a b -> (forall g. Coapply g => (g a -> b) -> g s -> t)
```

Note: `cloneTraversal` and `cloneCotraversal` require rank-2 carrier
types (`CotraversalRep`) or a VL round-trip. The VL variants are
more straightforward.

## S17.23 — Cotraversal0 constructors

The Cotraversal0 section only exports the type alias — no constructors,
no optics, no operators. Add:

```haskell
cotraversal0   :: (((s -> t + a) -> b) -> t) -> Cotraversal0 s t a b
cotraversalVl0 :: (forall f. Functor f => (forall c. f c -> c) -> (f a -> b) -> f s -> t) -> Cotraversal0 s t a b
cxtraversalVl0 :: (forall f. Functor f => (forall c. f c -> c) -> (f a -> k -> b) -> f s -> t) -> Cxtraversal0 k s t a b
cloneCotraversal0 :: ACotraversal0 s t a b -> Cotraversal0 s t a b
```

`cotraversal0` goes through the `Cotraversal0Rep` carrier.
`cotraversalVl0` is the VL form with a point-extraction witness.

## S17.24 — Missing indexed/coindexed Traversal operators

Traversal.hs operators have plain variants but are missing indexed
counterparts in several cases:

```haskell
-- Indexed variants of existing operators
ixsequenceOf :: Monoid k => Applicative f => AIxtraversal f k s t (f a) a -> s -> f t
ixmatchOf    :: Monoid k => AIxtraversal0 k s t a b -> s -> t + (k, a)
ixmapAccumLOf :: Monoid k => AIxtraversal (State r) k s t a b -> (k -> r -> a -> (r, b)) -> r -> s -> (r, t)
ixmapAccumROf :: Monoid k => AIxtraversal (Backwards (State r)) k s t a b -> (k -> r -> a -> (r, b)) -> r -> s -> (r, t)

-- Coindexed variant
cxcollectOf  :: Monoid k => Coapply f => ACxtraversal f k s t a (f a) -> f s -> t
```

Note: indexed `scanl1Of`/`scanr1Of` and indexed `reverseOf` are lower
priority — they're less commonly needed and can be composed from the
indexed `mapAccumLOf`/`mapAccumROf`.

## S17.25 — Ixprism/Rxprism family

Type aliases added to Types.hs (done this session). The full family
needs:

**Carrier.hs:**

```haskell
-- Carrier types
type AIxprism k s t a b = Ixoptic (PrismRep a b) k s t a b
type AIxprism' k s a = AIxprism k s s a a
type ARxprism k s t a b = Ixoptic (ReprismRep a b) k s t a b
type ARxprism' k s a = ARxprism k s s a a

-- No new carrier profunctors needed — PrismRep and ReprismRep
-- already have the right instances (Choice / Cochoice).

-- Carrier operators
withIxprism  :: Monoid k => AIxprism k s t a b -> ((s -> t + (k, a)) -> (b -> t) -> r) -> r
withRxprism  :: Monoid k => ARxprism k s t a b -> ((s -> (k, a)) -> (b -> (k, a) + t) -> r) -> r
```

**Prism.hs — Constructors:**

```haskell
ixprism  :: (s -> t + (k, a)) -> (b -> t) -> Ixprism k s t a b
ixprism' :: (s -> Maybe (k, a)) -> (b -> s) -> Ixprism k s s a b
ixhandling :: (s -> c + (k, a)) -> (c + b -> t) -> Ixprism k s t a b
cloneIxprism :: AIxprism k s t a b -> Ixprism k s t a b

rxprism  :: (s -> (k, a)) -> (b -> (k, a) + t) -> Rxprism k s t a b
rxprism' :: (s -> (k, a)) -> ((k, a) -> Maybe s) -> Rxprism' k s a
cloneRxprism :: ARxprism k s t a b -> Rxprism k s t a b
```

**Prism.hs — Optics:**

```haskell
ixleft  :: Ixprism k (a + c) (b + c) a b
ixright :: Ixprism k (c + a) (c + b) a b
ixjust  :: Ixprism k (Maybe a) (Maybe b) a b
```

**Prism.hs — Operators:**

```haskell
ixaside   :: AIxprism k s t a b -> Ixprism k (e, s) (e, t) (e, a) (e, b)
ixwithout :: AIxprism k s t a b -> AIxprism k u v c d -> Ixprism k (s + u) (t + v) (a + c) (b + d)
withIxprism :: ... (re-exported from Carrier)
```

**Property.hs:**

```haskell
tofrom_ixprism    :: Eq s => Ixprism' k s a -> s -> Bool
fromto_ixprism    :: Eq s => Eq a => Eq k => Ixprism' k s a -> a -> Bool
idempotent_ixprism :: Eq s => Eq a => Eq k => Ixprism' k s a -> s -> Bool

tofrom_rxprism    :: Eq a => Eq k => Rxprism' k s a -> a -> Bool
fromto_rxprism    :: Eq s => Eq a => Eq k => Rxprism' k s a -> s -> Bool
idempotent_rxprism :: Eq s => Eq a => Eq k => Rxprism' k s a -> a -> Bool
```

**Test/Carrier.hs:** Hedgehog tests for all of the above.

## S17.28 — Rename Review → Coview, add true Review

The current naming is inconsistent with the library's own conventions:

- `Re*` prefix = Re-dual (swaps `Strong ↔ Costrong`)
- `Co*` prefix = categorical co-dual (replaces `Strong` with `Closed`)

Current (wrong):

```
type Review t b = forall p. (Closed p, CoercingL p) => Optic' p t b     -- should be Coview
type Rxview k t b = forall p. (Closed p, CoercingL p) => Cxoptic' p k t b  -- should be Cxview
```

Correct:

```
type Coview t b = forall p. (Closed p, CoercingL p) => Optic' p t b      -- co-dual of View
type Cxview k t b = forall p. (Closed p, CoercingL p) => Cxoptic' p k t b
type Review t b = forall p. (Costrong p, CoercingL p) => Optic' p t b    -- Re-dual of View
type Rxview k t b = forall p. (Costrong p, CoercingL p) => Ixoptic' p k t b
```

Both use `Tagged` as carrier for the simple case (`b → t`), but the
constraint distinction matters for composition: `Coview` composes with
the `Closed` chain (Colens, Cotraversal), `Review` composes with the
`Costrong` chain (Relens).

**Renames:**

| Current | New |
|---|---|
| `Review` | `Coview` |
| `Rxview` | `Cxview` |
| `AReview` | `ACoview` |
| `ARxview` | `ACxview` |
| `review` | `coview` (operator in View.hs) |
| `reviews` | `coviews` |
| `rxview` | `cxview` |
| `rxviews` | `cxviews` |
| `rxfrom` | `cxfrom` |
| `cloneReview` | `cloneCoview` |
| `reuse` | `couse` |
| `reuses` | `couses` |

**New types and functions to add:**

```haskell
-- Types
type Review t b = forall p. (Costrong p, CoercingL p) => Optic' p t b
type Rxview k t b = forall p. (Costrong p, CoercingL p) => Ixoptic' p k t b

-- Carriers
type AReview t b = ???  -- needs investigation: what monomorphic carrier?
type ARxview k t b = ???

-- Constructors, operators, clones parallel to Coview
```

Note: the true `Review` carrier needs investigation. `Tagged` satisfies
`Costrong + CoercingL` but so does `RelensRep` (for monomorphic use).
The `AReview` carrier type may need to be `Optic' Tagged t b` (same
as current) or something new.

**Files affected:** Types.hs, Carrier.hs, View.hs, Fold.hs (cofoldMapOf
uses AReview-like patterns), Iso.hs (reover), Prism.hs (reprism docs),
Lens.hs (colens docs), Infix.hs, all container modules, test modules.

## S17.27 — Missing Setter constructors, clones, and indexed MTL operators

The TODO on line 207 of Setter.hs already flags the missing constructors.

**Missing constructors:**

```haskell
ixsetter1 :: ((i -> a -> b) -> a -> t) -> Ixsetter1 i a t a b
cxsetter  :: ((i -> a -> t) -> s -> t) -> Cxsetter i s t a t
cxsetter1 :: ((i -> a -> t) -> s -> t) -> Cxsetter1 i s t a t
```

**Missing clones:**

```haskell
cloneSetter     :: ASetter s t a b -> Setter s t a b
cloneIxsetter   :: AIxsetter k s t a b -> Ixsetter k s t a b
cloneCosetter   :: ACosetter s t a b -> Cosetter s t a b
cloneCxsetter   :: ACxsetter k s t a b -> Cxsetter k s t a b
```

**Missing indexed MTL operators:**

```haskell
ixassigns :: MonadState s m => Monoid i => Ixoptic (->) i s s a b -> (i -> b) -> m ()
ixmodifies :: MonadState s m => Monoid i => Ixoptic (->) i s s a b -> (i -> a -> b) -> m ()
```

## S17.26 — Missing indexed/coindexed View/Review API

```haskell
-- Clones
cloneIxview  :: Monoid k => AIxview k s a -> Ixview k s a
cloneRxview  :: ARxview k t b -> Rxview k t b

-- Optics
ixtupling :: AIxview k a1 s a1 -> AIxview k a2 s a2 -> Ixview k s (a1, a2)
rxsumming :: ARxview k t b1 -> ARxview k t b2 -> Rxview k t (b1 + b2)

-- MonadState (indexed)
ixuse  :: MonadState s m => Monoid k => AIxview k s a -> m (Maybe k, a)
ixuses :: MonadState s m => Monoid k => Ixoptic' (Star (Const r)) k s a -> (k -> a -> r) -> m r

-- MonadState (coindexed)
rxreuse  :: MonadState b m => ARxview k t b -> m (k -> t)
rxreuses :: MonadState b m => ARxview k t b -> ((k -> t) -> r) -> m r
```

## Work order

Phase 1 — Validate constraint fix:
  1. S17.3 (Cofold predicates)
  2. S17.7 (Cofold hedgehog tests)
  3. S17.15 (unused import cleanup)
  4. S17.14 (dead CPP guards)

Phase 2 — Property coverage:
  5. S17.1 (uncomment compose_cotraversal)
  6. S17.2 (Cosetter laws)
  7. S17.4 (Traversal1 predicates)
  8. S17.6, S17.8 (Traversal, Cosetter hedgehog tests)

Phase 3 — Indexed coverage:
  9. S17.5 (indexed predicates)
  10. S17.9 (indexed hedgehog tests)

Phase 4 — Fold API:
  11. S17.10 (boolean queries)
  12. S17.11 (numeric aggregations)
  13. S17.12 (search and extrema)
  14. S17.13 (head/last)

Phase 5 — API completeness:
  15. S17.19 (missing Fold constructors and optics)
  16. S17.20 (Rxlens constructors)
  17. S17.21 (missing clone/VL in Lens.hs)
  18. S17.22 (missing clone functions in Traversal.hs)
  19. S17.23 (Cotraversal0 constructors)
  20. S17.24 (missing indexed/coindexed Traversal operators)
  21. S17.25 (Ixprism/Rxprism full family)
  22. S17.26 (indexed/coindexed View/Review API)
  23. S17.27 (Setter constructors, clones, indexed MTL)
  24. S17.28 (Review → Coview rename, add true Review)

## Key files

- `profunctor-optics/src/Data/Profunctor/Optic/Types.hs`
- `profunctor-optics/src/Data/Profunctor/Optic/Property.hs`
- `profunctor-optics/src/Data/Profunctor/Optic/Fold.hs`
- `profunctor-optics/test/Test/Carrier.hs`
- `profunctor-optics/test/test.hs`

## Dependencies

No new dependencies. All fold query functions use `Data.Monoid`
and `Data.Semigroup` which are already imported.

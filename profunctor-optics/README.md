[Hackage link](http://hackage.haskell.org/package/profunctor-optics)

This package provides utilities for creating and manipulating profunctor-based optics. Some highlights:
 
  * Full complement of isos, co/prisms, co/lenses, grates, co/traversals (affine, regular, and non-empty), co/folds (affine, regular, and non-empty), co/views, and co/setters.

  * Composable indexed and co-indexed variants of all of the above.

  * Compact & straight-forward implementation. No inscrutable internal modules, lawless or otherwise ancillary typeclasses, or heavy type-level machinery. The language extensions doing the majority of the work are `RankNTypes` and `QuantifiedConstraints`.

  * Fully interoperable. All that is required to create optics (standard, idexable, or co-indexable) is the `profunctors` package, which is heavily used and likely to end up in `base` at some point. Optics compose with `(.)` from `Prelude` as is typical. If you want to provide profunctor optics for your own types in your own libraries, you can do so without incurring a dependency on this package. Conversions to & from the Van Laarhoven representations are provided for each optic type.

  * Well-documented properties and exportable predicates for testing your own optics.


If you're new to profunctors, [this talk](https://www.youtube.com/watch?v=OJtGECfksds) by Phil Freeman and the following series are good general introductions:

- [Don't Fear the Profunctor Optics, part 1](https://github.com/hablapps/DontFearTheProfunctorOptics/blob/master/Optics.md)
- [Don't Fear the Profunctor Optics, part 2](https://github.com/hablapps/DontFearTheProfunctorOptics/blob/master/Profunctors.md)
- [Don't Fear the Profunctor Optics, part 3](https://github.com/hablapps/DontFearTheProfunctorOptics/blob/master/ProfunctorOptics.md)

For the more mathematically inclined, [this post](http://blog.sigfpe.com/2011/07/profunctors-in-haskell.html) by Dan Piponi is great. Oleg Grenrus also has several blog excellent blog posts (notably [this one](http://oleg.fi/gists/posts/2017-04-18-glassery.html) that provide a synthesis of the Pickering, Gibbons, and Wu paper for Haskellers.

The theory behind profunctor optics is well-described in the following papers:

- [Profunctor Optics: Modular Data Accessors](https://arxiv.org/abs/1703.10857) by Pickering, Gibbons, and Wu
- [What You Needa Know about Yoneda](https://www.cs.ox.ac.uk/jeremy.gibbons/publications/proyo.pdf) by Gibbons and Boisseau

`profunctor-optics` is based on prior work by: Ed Kmett, Russell O’Connor, Twan van Laarhoven, and many others. Several papers, posts, and talks by Jeremy Gibbons, Matthew Pickering, Oleg Grenrus, Guillaume Boisseau, and others were also invaluable.

## Overview

Optics libraries generally consist of three components:

- Rank-2 types representing the families of optic (e.g. `Lens`, `Prism`, etc.).
- Functions for constructing optics (e.g. `lens`, `prism`, etc.)
- Particular 'carriers' (e.g.`LensRep a b s t`,  `(a -> Const r b) -> s -> Const r t`, `Cokleisli f s a`, `Int -> Int`, etc) 
- Primitive operators derived by using the optics to manipulate the carriers (`withLens`, `withFold`, etc.)
- Particular optics (e.g. `_1`, `just`, `traversed`, etc.)
- Operators derived by various applications of the primitive operators (e.g. `^..`, `view`, `set`, `throws`, etc)

`profunctor-optics` is organized by family (and its [dual](#duality) if available). Each module consists of one or more sections for each of the components above. 

There are several additional modules within the main `Data.Profunctor.Optic` namespace:

- `Data.Profunctor.Optic.Types` contains all of the optic family definitions.
- `Data.Profunctor.Optic.Index` contains functions for manipulating (co-)indexed optics, as well as the definitions of `Index` and `Coindex`.
- `Data.Profunctor.Optic.Property` contains predicates for use with property-based testing libraries such as `quickcheck` or `hedgehog`.
- `Data.Profunctor.Optic.Operator` re-exports some of the more commonly used operators.

Finally there are several additional namespaces containing domain-specific optics. For example:

- `Control.Exception.Optic`
- `Data.Connection.Optic`

### Hierarchy

There is lattice of entailment relations between the various families of optic. Each node in the lattice corresponds to a conjunction of type class constraints on a function of the type `p a b -> p s t` (for general optics), `p (i , a) b -> p (i , s) t` (for indexed optics), or `p a (k -> b) -> p s (k -> t)` (for coindexed optics).

For example, in the middle of hierarchy is `Traversal0` (also known as an 'affine' traversal):

```
type Traversal0 s t a b = forall p. Strong p => Choice p => Optic p s t a b 
```

`Traversal0`s relate to structures containing aspects of both sum and product types ([These](https://hackage.haskell.org/package/these-1.0.1/docs/Data-These.html#t:These) is a basic example). The indexed variant is particularly useful in concert with indexed containers:

```
inserted Map.lookupGT Map.insert :: Ord i => i -> Ixtraversal0' i (Map i a) a
```

Imposing two additional constraints on a `Traversal0` (using the `Representable` typeclass from `profunctors`) gives us the familiar `Traversal`:

```
type Traversal s t a b = forall p. Strong p => Choice p => Representable p => Applicative (Rep p) => Optic p s t a b 
```

The other way to add constraints of course is to simply compose optics

```
>>> :t left . first
left . first :: (Choice p, Strong p) => p a b -> p ((a, c1) + c2) ((b, c1) + c2)
```

Each time we add a constraint, the corresponding set of optics gains some additional capabilities across a narrower class of structures. 

Finally note that intra-module imports also follow the entailment DAG. So for example an operator with `Profunctor` and `Choice` constraints will be located in `Data.Profunctor.Optic.Prism` (i.e. in the module corresponding to the conjuction of the constraints). 

### A note on naming

`profunctor-optics` generally re-uses names from `lens-family` & `lens`. It does diverge in a few places in order to favor simplicity and internal consistency.

#### Types

Names of types are essentially the same as in `lens`. The most significant difference is that `Getter` is `View` and `Getting` is `AFold`.

#### Constructors

Constructors are either named after the type itself (e.g. `traversal`), the present participle of the root (e.g. `traversing`), or the type with a `Vl` suffix (e.g. `traversalVl`). Naming is done consistently according to the following rules.

Constructors named after the type are reserved for translations from the direct representation to the profunctor representation of an optic of that type. For example:

```
iso :: (s -> a) -> (b -> t) -> Iso s t a b
grate :: (((s -> a) -> b) -> t) -> Grate s t a b
setter :: ((a -> b) -> s -> t) -> Setter s t a b
lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
colens :: (b -> s -> a) -> (b -> t) -> Colens s t a b
traversal :: Traversable f => (s -> f a) -> (s -> f b -> t) -> Traversal s t a b
cotraversal :: Distributive g => (g b -> s -> g a) -> (g b -> t) -> Cotraversal1 s t a b
fold_ :: Foldable f => (s -> f a) -> Fold s a
prism :: (s -> t + a) -> (b -> t) -> Prism s t a b
prism' :: (s -> Maybe a) -> (a -> s) -> Prism' s a
traversal0 :: (s -> t + a) -> (s -> b -> t) -> Traversal0 s t a b
traversal0' :: (s -> Maybe a) -> (s -> a -> s) -> Traversal0' s a
```

The only exceptions to this rule are `View` and `Review` (whose basic constructors are `to` and `from`). This is to keep the names of oft-used functions in line with their counterparts in `lens`. Also worth noting is that the order of the arguments in `prism` agree with those in the `lens-family` [version](http://hackage.haskell.org/package/lens-family-2.0.0/docs/Lens-Family2-Unchecked.html#v:prism), rather than the `lens` version. This is to keep the argument ordering consistent amongst the expanded range of constructors.


Constructors named with the present participle of the type itself occur only in (co-)representable optics, and are reserved for constructors that lift direct representations of substructures into the whole. For example:

```  
folding :: Traversable f => (s -> a) -> Fold (f s) a
folding1 :: Traversable1 f => (s -> a) -> Fold1 (f s) a
cofolding1 :: Distributive f => (b -> t) -> Cofold1 (f t) b
traversing :: Traversable f => (s -> a) -> (s -> b -> t) -> Traversal (f s) (f t) a b
cotraversing1 :: Distributive g => (b -> s -> a) -> (b -> t) -> Cotraversal1 (g s) (g t) a b
cotraversing1 :: Distributive g => (((s -> a) -> b) -> t) -> Cotraversal1 (g s) (g t) a b
```

In some cases there are additional constructors using an alternative present participle (e.g. `cotraversing`, `matching`, `handling`, `fmapping`, `contramapping`, `failing`, etc). Other than the consistent use of the present participle these constructors mirror the ones in `lens`.

Constructors ending in `Vl` are reserved for translations from the [Van Laarhoven](https://www.twanvl.nl/blog/haskell/cps-functional-references) representation to the profunctor representation. For example:

```
isoVl :: (forall f g. Functor f => Functor g => (g a -> f b) -> g s -> f t) -> Iso s t a b
foldVl :: (forall f. Applicative f => (a -> f b) -> s -> f t) -> Fold s a
lensVl :: (forall f. Functor f => (a -> f b) -> s -> f t) -> Lens s t a b
grateVl :: (forall f. Functor f => (f a -> b) -> f s -> t) -> Grate s t a b
colensVl :: (forall f. Functor f => (t -> f s) -> b -> f a) -> Colens s t a b
traversal1Vl :: (forall f. Apply f => (a -> f b) -> s -> f t) -> Traversal1 s t a b
cotraversal1Vl :: (forall f. Apply f => (f a -> b) -> f s -> t) -> Cotraversal1 s t a b
```

Any optic in `lens-family` can be lifted into its profunctor representation using one of these constructors. The same goes for any `LensLike` optic in `lens` (prisms and isos in `lens` are hybrid representations).

#### Optics

The past participle is reserved for naming optics (e.g. `swapped`, `summed`, `traversed`, etc).  

```
united :: Lens' a ()
voided :: Lens' Void a
zipped :: Setter (u -> v -> a) (u -> v -> b) a b
inserted :: (i -> s -> Maybe (i, a)) -> (i -> a -> s -> s) -> i -> Ixtraversal0' i s a
```

Optics derived via direct applications of a constructor are named with the past participle of the constructor. For example

```
folded :: Traversable f => Fold (f a) a
folded_ :: Foldable f => Fold (f a) a
folded1_ :: Foldable1 f => Fold1 (f a) a
cofolded1 :: Distributive f => Cofold1 (f b) b
traversed :: Traversable f => Traversal (f a) (f b) a b
bitraversed :: Bitraversable f => Traversal (f a a) (f b b) a b
cotraversed1 :: Distributive f => Cotraversal1 (f a) (f b) a b 
```

Where possible, the verb itself refers to the action of moving from `s` to `a`. For example:

```
coerced :: Coercible s a => Coercible t b => Iso s t a b
curried :: Iso ((a , b) -> c) ((d , e) -> f) (a -> b -> c) (d -> e -> f)
branched :: Lens' (Tree a) [Tree a]
unlifted :: MonadUnliftIO m => Grate (m a) (m b) (IO a) (IO b)
```

Prisms corresponding to a constructor take the name of that constructor. For example:

```
left :: Prism (a + c) (b + c) a b
just :: Prism (Maybe a) (Maybe b) a b
cxjust :: (k -> Maybe b) -> Cxprism k (Maybe a) (Maybe b) a b
asyncException :: Exception e => Prism' SomeException e
```

#### Operators

Primary operators are derived by pushing a carrier type (e.g. `Star`, `GrateRep`) through an optic. These operators are either prefixed with `with` or suffixed with `Of`. For example:

```
constOf :: AGrate s t a b -> b -> t
zipWithOf :: AGrate s t a b -> (a -> a -> b) -> s -> s -> t
withGrate :: AGrate s t a b -> ((((s -> a) -> b) -> t) -> r) -> r
withTraversal :: Applicative f => ATraversal f s t a b -> (a -> f b) -> s -> f t
cowithFold1 :: ACofold1 r t b -> (r -> b) -> r -> t
withIxfold0 :: AIxfold0 r i s a -> (i -> a -> Maybe r) -> i -> s -> Maybe r
```

Secondary operators are derived from applications of primary operators and are generally named using the (first or third-person) simple present tense. For example:

```
is :: ATraversal0 s t a b -> s -> Bool
match :: ATraversal0 s t a b -> s -> t + a
use :: MonadState s m => AView s a -> m a
set :: ASetter s t a b -> b -> s -> t
reset :: AResetter s t a b -> b -> s -> t
view :: MonadReader s m => AView s a -> m a
reviews :: MonadReader b m => AReview t b -> (t -> r) -> m r
foldsr :: AFold (Endo r) s a -> (a -> r -> r) -> r -> s -> r
finds :: AFold (Endo (Maybe a)) s a -> (a -> Bool) -> s -> Maybe a
hasnt :: AFold All s a -> s -> Bool
modifies :: MonadState s m => ASetter s s a b -> (a -> b) -> m ()
```

The primary exceptions to this rule are `over` and `under`, again done for compatibility with `lens` and [`lens-family`](http://hackage.haskell.org/package/lens-family-core-2.0.0/docs/Lens-Family.html#v:under).


### Indexed & Coindexed versions

Many types, optics, and operators come in either indexed or coindexed versions. Indexed versions are prefaced with `Ix` or `ix`, and coindexed versions with `Cx` or `cx`. For example:

```
type Ixlens i s t a b = forall p. Strong p => IndexedOptic p i s t a b
cxviews :: MonadReader b m => ACxview k t b -> ((k -> t) -> r) -> m r
ixlists :: Monoid i => AIxfold (Endo [(i, a)]) i s a -> s -> [(i, a)]
ixlistsFrom :: AIxfold (Endo [(i, a)]) i s a -> i -> s -> [(i, a)]
cxgrateVl :: (forall f. Functor f => (k -> f a -> b) -> f s -> t) -> Cxgrate k s t a b
cxtraversal1Vl :: (forall f. Apply f => (k -> f a -> b) -> f s -> t) -> Cxtraversal1 k s t a b
```

Co-indexed [duals](#duality) of optics are prefaced with `Cx` (rather than say `IxCo`) to avoid piling up prefixes.

For infix operators, indexed versions substitute `.` for `%` and coindexed versions substitute `/` for `#`. For example:

```
(^.) :: s -> AView s a -> a
(^%) ::  Monoid i => s -> AIxview a i s a -> (Maybe i , a)
(.~) :: ASetter s t a b -> b -> s -> t
(%~) :: Monoid i => AIxsetter i s t a b -> (i -> b) -> s -> t
(/~) :: AResetter s t a b -> b -> s -> t
(^..) :: s -> AFold (Endo [a]) s a -> [a]
(^%%) :: Monoid i => s -> AIxfold (Endo [(i, a)]) i s a -> [(i, a)]
(..~) :: ASetter s t a b -> (a -> b) -> s -> t
(%%~) :: Monoid i => AIxsetter i s t a b -> (i -> a -> b) -> s -> t
(//~) :: AResetter s t a b -> (a -> b) -> s -> t
(##~) :: Monoid k => ACxsetter k s t a b -> (k -> a -> b) -> s -> t
```

Note that `(%~)` is an indexed `set`, not an infix `over`.

Indexed and coindexed optics compose with `.` from `Prelude`, using `Data.Semigroup.Last` semantics (i.e. we retain the right/innermost index):

```
>>> ixlists (ix @Int traversed . ix traversed) ["foo", "bar"]
[(0,'f'),(1,'o'),(2,'o'),(0,'b'),(1,'a'),(2,'r')]
```

In cases where you want to use some other semigroup operation to compose, use `%` or `#`:
```
(#) :: Semigroup k => CxrepnLike p k b1 b2 a1 a2 -> CxrepnLike p k c1 c2 b1 b2 -> CxrepnLike p k c1 c2 a1 a2
(%) :: Semigroup i => IxrepnLike p i b1 b2 a1 a2 -> IxrepnLike p i c1 c2 b1 b2 -> IxrepnLike p i c1 c2 a1 a2
```

Using these composition operators with `Last` reduces to the standard case above:
```
>>> ixlistsFrom (ixlast (ix @Int traversed) % ixlast (ix traversed)) (Last 0) ["foo", "bar"] & fmapped . first ..~ getLast
[(0,'f'),(1,'o'),(2,'o'),(0,'b'),(1,'a'),(2,'r')]
```

### Duality

In category theory and in some Haskell libraries it is common to refer to the 'dual' of something, often with the prefix 'co' (e.g. 'cotraverse').
The 'dual' of a given type is usually obtained by reversing some or all of the arrows in the original type signature. This is a useful shorthand, 
but it can sometimes be confusing if it's not clear what the category is (essentially which arrows are to be reversed).

There are three different kinds of duality occuring in optics, one for each of the three optic representations.

#### (Co-)product duality

The first kind arises when you swap out products for coproducts, which is itself a reversing of arrows (consider `fst :: (a , b) -> a` vs `Left :: a -> (a + b)`).
This gives rise to the lens/prism relationship:

```
matching :: (s -> (c , a)) -> ((c , b) -> t) -> Lens s t a b
handling :: (s -> (c + a)) -> ((c + b) -> t) -> Prism s t a b
```

Each of these has its own indexed variant, prefaced with `Ix` and `Ex` respectively.

#### Van Laarhoven duality

The second kind arises when you reverse arrows in the Van Laarhoven representation. This gives rise to the lens/grate relationship:

```
lensVl :: (forall f. Functor f => (a -> f b) -> s -> f t) -> Lens s t a b
grateVl :: (forall f. Functor f => (f a -> b) -> f s -> t) -> Grate s t a b 
```

Also the 'Traversal1' / 'Cotraversal1' relationship:
```
traversal1Vl :: (forall f. Apply f => (a -> f b) -> s -> f t) -> Traversal1 s t a b
cotraversalVl :: (forall f. Apply f => (f a -> b) -> f s -> t) -> Cotraversal1 s t a b
```

... and the `Fold1` / `Cofold1` relationship:

```
folding1 :: Traversable1 f => (s -> a) -> Fold1 (f s) a
cofolding1 :: Distributive f => (a -> s) -> Cofold1 (f s) a
```

#### Profunctor duality

The final kind of duality arises when you reverse arrows in the profunctor representation. This gives rise to the `Lens`/`Colens` relationship:

```
first :: forall p. Strong p => p a b -> p (a, c) (b, c)
refirst :: forall p. Costrong p => p (a, c) (b, c) -> p a b
```

This can also be expressed at the first level 

```
matching :: (s -> (c , a)) -> ((c , b) -> t) -> Lens s t a b
rematching :: ((c , s) -> a) -> (b -> (c , t)) -> Colens s t a b
```

... and in terms of prisms:
```
handling :: (s -> c + a) -> (c + b -> t) -> Prism s t a b
rehandling :: (c + s -> a) -> (b -> c + t) -> Coprism s t a b
```

For compatibility with other packages (e.g. `lens`, `lens-family`), the prefix `Re` is used in someplaces rather than `Co` (e.g. `Review`, `Resetter`, etc).

This third form is particularly useful because, unlike the first two, the arrows can be flipped programaticaly. 
This leads to a number of useful relationships:

```
refirst ≡ re first
releft ≡ re left
relike ≡ re . like
reover ≡ over . re
reset ≡ set . re
review ≡ view . re
reuse ≡ use . re
...
set . re $ re (lens f g) ≡ g
relens f g ≡ \f g -> re (lens f g)
...

```

The reflexive nature of duality is witnessed by the fact that the function `re` is involutive (i.e. is its own inverse):

```
λ> :t first
first :: Strong p => Optic p (a, c) (b, c) a b
λ> :t re . re $ first
re . re $ first :: Strong p => Optic p (t, c) (s, c) t s
λ> :t refirst
refirst :: Costrong p => Optic p a b (a, c) (b, c)
λ> :t re . re $ refirst
re . re $ refirst :: Costrong p => Optic p b a (b, c) (a, c)
```

Finally, note that for optics arising from (co-)representable profunctors, the second and third forms of duality are equivalent.

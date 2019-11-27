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

## A note on duality and naming

In category theory and in some Haskell libraries it is common to refer to the 'dual' of something, often with the prefix 'co' (e.g. 'cotraverse').
The 'dual' of a given type is usually obtained by reversing some or all of the arrows in the original type signature. This is a useful shorthand, 
but it can sometimes be confusing if it's not clear what the category is (essentially which arrows are to be reversed).

There are three different kinds of duality occuring in optics, one for each of the three optic representations.

### (Co-)product duality

The first kind arises when you swap out products for coproducts, which is itself a reversing of arrows (consider `fst :: (a , b) -> a` vs `Left :: a -> (a + b)`).
This gives rise to the lens/prism relationship:

```
matching :: (s -> (c , a)) -> ((c , b) -> t) -> Lens s t a b

handling :: (s -> (c + a)) -> ((c + b) -> t) -> Prism s t a b
```

Each of these has its own indexed variant, prefaced with `Ix` and `Ex` respectively.

### Van Laarhoven duality

The second kind arises when you reverse arrows in the Van Laarhoven representation. This gives rise to the lens/grate relationship:

```
lensVl :: (forall f. Functor f => (a -> f b) -> s -> f t) -> Lens s t a b

grateVl :: (forall f. Functor f => (f a -> b) -> f s -> t) -> Grate s t a b 
```

Also the 'Traversal' / 'Cotraversal' relationship:
```
traversing :: (forall f. Applicative f => (a -> f b) -> s -> f t) -> Traversal s t a b
	
cotraversing :: (forall f. Comonad f => (f a -> b) -> f s -> t) -> Cotraversal s t a b
```

... and the `Fold` / `Cofold` relationship:

```
folding :: Traversable f => (s -> a) -> Fold (f s) a

cofolding :: Distributive f => (a -> s) -> Cofold (f s) a
```

Co-indexed optics are prefaced with `Cx` (rather than say `IxCo`) to avoid piling up prefixes. 

### Profunctor duality

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

[Hackage link](http://hackage.haskell.org/package/profunctor-optics)

This package provides utilities for creating and manipulating profunctor-based optics. Some highlights:
 
  * Full complement of isos, prisms, lenses, grates, affines, traversals, cotraversals, views, setters, folds, and more. 

  * Composable indexed or co-indexed variants of most of the above.

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

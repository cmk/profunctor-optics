[Hackage link](http://hackage.haskell.org/package/profunctor-optics)

This package provides some utilities for manipulating profunctor-based optics. It has a few goals:

  * Be simple. Optics are complex enough without adding implementation noise. There are no inscrutable internal modules, lawless or otherwise ancillary typeclasses, or heavy type-level machinery. The language extensions doing the majority of the work are `RankNTypes` and `QuantifiedConstraints`.

  * Be correct. Optics have clear laws that should be tested in cases when they are written by hand. Operators should obey the <https://en.wikipedia.org/wiki/Principle_of_least_astonishment principle of least astonishment> and generate type errors when presented with an incompatible optic rather than do something sneaky.
 
  * Be flexible. Profunctor optics are an area of active exploration, and new optics and use cases are still being discovered. Corepresentable optics for example have use cases in rounding and resource handling that remain largely unexplored. Therefore it's useful not to over-prescribe a hierarchy.

  * Be performant. Pure data access and mutation shouldn't be the bottleneck in your application.

  * Be interoperable. The only requirement to creat an optic is the `profunctors` package, which is heavily used and likely to end up in `base` at some point. Optics compose with `(.)` from `Prelude` as is typical. If you want to provide profunctor optics for your own types in your own libraries, then you can do so without incurring a dependency on this package. The same goes for indexed and coindexed optics. Conversions to & from the Van Laarhoven representations are provided for each optic type.

If you're new to profunctors, [this talk](https://www.youtube.com/watch?v=OJtGECfksds) by Phil Freeman and the following series are good general introductions:

- [Don't Fear the Profunctor Optics, part 1](https://github.com/hablapps/DontFearTheProfunctorOptics/blob/master/Optics.md)
- [Don't Fear the Profunctor Optics, part 2](https://github.com/hablapps/DontFearTheProfunctorOptics/blob/master/Profunctors.md)
- [Don't Fear the Profunctor Optics, part 3](https://github.com/hablapps/DontFearTheProfunctorOptics/blob/master/ProfunctorOptics.md)

For the more mathematically inclined, [this post](http://blog.sigfpe.com/2011/07/profunctors-in-haskell.html) by Dan Piponi is great. Oleg Grenrus also has several blog excellent blog posts (notably [this one](http://oleg.fi/gists/posts/2017-04-18-glassery.html) that provide a synthesis of the Pickering, Gibbons, and Wu paper for Haskellers.

The theory behind profunctor optics is well-described in the following papers:

- [Profunctor Optics: Modular Data Accessors](https://arxiv.org/abs/1703.10857) by Pickering, Gibbons, and Wu
- [What You Needa Know about Yoneda](https://www.cs.ox.ac.uk/jeremy.gibbons/publications/proyo.pdf) by Gibbons and Boisseau

`profunctor-optics` is based on prior work by: Ed Kmett, Russell O’Connor, Twan van Laarhoven, and many others. Several papers, posts, and talks by Jeremy Gibbons, Matthew Pickering, Oleg Grenrus, Guillaume Boisseau, and others were also invaluable.

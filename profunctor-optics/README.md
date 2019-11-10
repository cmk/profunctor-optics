[Hackage link](http://hackage.haskell.org/package/profunctor-optics)

`profunctor-optics` is based on prior work by: Ed Kmett, Russell O’Connor, Twan van Laarhoven, Phil Freeman, Oleg Grenrus, and many others. Several papers and talks by Jeremy Gibbons, Matthew Pickering, Guillaume Boisseau, and Brendan Fong were also invaluable.

The goal here is to provide a semantically precise and performant implementation of profunctor optics, based on the `profunctors` package and suitable for application development.

Why a profunctor optics library? Several reasons:

- It's much cleaner to start with profunctors, and a dependency on `profunctors` no longer seems like as much of an imposition as it did in 2011.
- There are many useful classes of optic not easily expressible in the Van Laarhoven style.
- I found certain aspects of `lens` frustrating to use for application development.

If you're new to profunctors, [this talk](https://www.youtube.com/watch?v=OJtGECfksds) by Phil Freeman and the following series are good general introductions:

- [Don't Fear the Profunctor Optics, part 1](https://github.com/hablapps/DontFearTheProfunctorOptics/blob/master/Optics.md)
- [Don't Fear the Profunctor Optics, part 2](https://github.com/hablapps/DontFearTheProfunctorOptics/blob/master/Profunctors.md)
- [Don't Fear the Profunctor Optics, part 3](https://github.com/hablapps/DontFearTheProfunctorOptics/blob/master/ProfunctorOptics.md)

For the more mathematically inclined, [this post](http://blog.sigfpe.com/2011/07/profunctors-in-haskell.html) by Dan Piponi is great. Oleg Grenrus also has several blog excellent blog posts (notably [this one](http://oleg.fi/gists/posts/2017-04-18-glassery.html) that provide a synthesis of the Pickering, Gibbons, and Wu paper for Haskellers.

The theory behind profunctor optics is well-described in the following papers:

- [Profunctor Optics: Modular Data Accessors](https://arxiv.org/abs/1703.10857) by Pickering, Gibbons, and Wu
- [What You Needa Know about Yoneda](https://www.cs.ox.ac.uk/jeremy.gibbons/publications/proyo.pdf) by Gibbons and Boisseau 

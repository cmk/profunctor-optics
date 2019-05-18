[poptic](https://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/poptics.pdf)

This library is based in large part on 

- Edward Kmett's [`profunctors`](http://hackage.haskell.org/package/profunctors) and [`lens`](http://hackage.haskell.org/package/lens) libraries
- [Profunctor Optics: Modular Data Accessors](https://arxiv.org/abs/1703.10857) by Matthew Pickering et al
- [Glassery](http://oleg.fi/gists/posts/2017-04-18-glassery.html) by Oleg Grenrus

Its purpose is to provide a minimal & performant implementation of profunctor-encoded optics. Why? 
Mainly because the profunctor encoding of optics is easier to understand and work with than the van Laarhoven encoding. 
This is especially true if you need a lot of control over the entailment relationships between different classes of optic.
Such a need arose during the creation of [`pref`](https://github.com/cmk/putil/tree/master/pref), which is what led to this work in the first place. 

Now onto the library. If you're new to profunctors, [this post](http://blog.sigfpe.com/2011/07/profunctors-in-haskell.html) and [this talk](https://www.youtube.com/watch?v=OJtGECfksds) are excellent general introductions. 
There's also some more detailed mathematical background on the [nLab](https://ncatlab.org/nlab/show/profunctor) page.

## Intro

For day-to-day usage there are four components to keep in mind:

- profunctor type classes (e.g. `Profunctor`, `Strong`, `Choice`, `Closed` etc.)
- particular profunctors (e.g. `Star (Const Int) Text Text`, `Costar Maybe a b`, `Costar (Const c) a b`, `Star (Const c) a b c`, etc.)
- optic 'classes' (e.g. `Lens`, `Prism`, `Affine`, `Traversal`, `Grate` etc.), induced by entailment relations between the classes above
- particular optics (e.g. `_1 :: Strong p => Optic p (a, c) (b, c) a b`)
- operators on optics (e.g. `.`, `re`, `to`, `view`, `matching`, `traverseOf`, etc.)


The lattice of entailment relations between the various profunctor type classes is a good place to start. 
It looks like this:

<div class="text-center">
<img title="optics diagram" src="./optics-hierarchy.svg" />
</div>

Credit to Oleg I think for the diagram.
Each node in the lattice corresponds to a conjunction of type class constraints on a function of the type `p a b -> p s t`.
For example, at the bottom (top in the diagram) of the hierarchy is a `Setter`, also known as a [semantic editor combinator](http://conal.net/blog/posts/semantic-editor-combinators).
Setters have the following type 

```
type Setter s t a b = forall p. c p => p a b -> p s t
``` 

where the constraint `c` is given by the conjunction of the `Profunctor`, `Strong`, `Choice`, `Traversing`, `Closed`, and `Mapping` type classes.
 
At the top of the hierarchy is an `Iso`, which is restricted only by the `Profunctor` constraint.
Imposing an additional `Strong` (<span style="color:#000080">blue</span>) constraint we get `Lens`,
and adding `Traversing1` (<span style="color:#008000">green</span>) turns a `Lens` into a `Traversal1`.
The other colors denote `Choice` (<span style="color:#800000">red</span>),
`OutPhantom` (<span style="color:#ff8000">orange</span>),
`InPhantom` (<span style="color:#8000ff">purple</span>), and
`Mapping` (<span style="color:#808080">gray</span>). 
Note that `Closed` is missing, as is `Traversing`, though `Traversing` is (almost) the combination of `Traversing1` and `Choice`.
The `Strong` (left) side of the graph can also be indexed, leading to `IndexedLens`, `IndexedTraversal` etc. 


For each optic there is a 'constructor' and characterizing operators, which are analogous to the introduction and elimination rules in logic. 
For example, for lenses:

```
lens (view l) (set l) ≡ l
      view (lens g s) ≡ g
       set (lens g s) ≡ s
```

Compare with the local soundness and completeness of conjunction:

```
pair (fst p) (snd p) ≡ p  -- complete
      fst (pair x y) ≡ x  -- sound 1
      snd (pair x y) ≡ y  -- sound 2
```

The constructors and characterizing operations for the remaining optics are summarized in the following table:

| Optic | Constructor | Operators | Constraint | Profunctor |
| --- | --- | --- | --- | --- |
| [Equality](#equality)                 | `id`            |                      |                     |               |
| [Iso](#iso)                           | `iso`           | `view`, `review`     | `Profunctor`        |               |
| [Lens](#lens)                         | `lens`          | `view`, `set`        | `Strong`            |               |
| [Prism](#prism)                       | `prism`         | `matching`, `review` | `Choice`            |               |
| [Affine Traversal](#affine-traversal) | `affine`        | `matching`, `set`    | `AffineTraversing`  | `Matched`       |
| [PrimGetter](#getter)                 | `to`            | `view`               | `OutPhantom`        | `Star (Const c)` |
| [Getter](#getter)                     | `to`            | `view`               | `Getting`           | `Star (Const c)` |
| [PrimSetter](#setter)                 | `setting`       | `over`               | `InPhantom`         | `(->)`        |
| [Setter](#setter)                     | `setting`       | `over`               | `Mapping`           | `(->)`        |
| [Review](#review)                     | `unto`          | `review`             | `Reviewing`         | `Costar (Const c)`      |
| [Traversal](#traversal)               | `traversing`    | `traverseOf`         | `Traversing`        | `Star`        |
| [Affine Fold](#fold-and-affine-fold)  | `afolding`      | `preview`            | `AffineFolding`     | `Previewed`   |
| [Fold](#fold-and-affine-fold)         | `folding`       | `foldMapOf`          | `Folding`           | `Star (Const c)` |
| [Closure](#closure)                   | `closed`        | `zipWithOf`          | `Closed`            | `Zipped`      |

The laws are captured in property-driven tests in the test folder.  
Predicates describing the laws are kept separate so that they can be used to verify downstream optics.

The operators themselves are for the most part created from the associated profuctor (e.g. `review` from `Costar (Const c)`) in a standard fashion:

```

```

See the `Data.Profunctor.Optic.Operator` module for more detail. 



Finally, the relationships between the associated profunctors and the profunctor classes is as follows:

| | `Star (Const c)` | `Star` | `Costar (Const c)` | `Zipped` | `Matched` | `Previewed` |  `(->)` |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `Profunctor`      | **yes** | **yes** | **yes** | **yes** | **yes** | **yes** | **yes** |
| `InPhantom`       | no      | no      | **yes** | no      | no      | no      | no      |
| `OutPhantom`      | **yes** | no      | no      | no      | no      | **yes** | no      |
| `Strong`          | **yes** | **yes** | no      | **yes** | **yes** | **yes** | **yes** |
| `Costrong`        | **yes** | no      | **yes** | **yes** | **yes** | no      | **yes** |
| `Choice`          | monoid  | aplctve | **yes** | **yes** | **yes** | **yes** | **yes** |
| `Cochoice`        | **yes** | aplctve | no      | **yes** | no      | no      | **yes** | 
| `Traversing`      | monoid  | aplctve | no      | no      | no      | no      | **yes** |
| `Mapping`         | no      | aplctve | no      | no      | no      | no      | **yes** |
| `Closed`          | **yes** | dstrbve | **yes** | **yes** | no      | no      | **yes** |



where annotated entries indicate that the instance is entailed by constraints on the underlying functor. 
This chart in turn is what determines which operators can be used with each optic.

Consider `review` for example, which is derived from the `Costar (Const c)` profunctor. `Costar (Const c)` is not an instance of the `Strong`, `Traversing`, `Closed`, or `Mapping` classes. It follows then that a `Setter`, which as we noted above is constrained by `Profunctor`, `Strong`, `Choice`, `Traversing`, `Closed`, and `Mapping`, will not be compatible with the `review` operator.



## Optics


### Grate

Grates were (afaik) originally introduced on Russel O'Connor's [blog](https://r6research.livejournal.com/28050.html).

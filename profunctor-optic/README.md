
This library is based in large part on Edward Kmett's
[`lens`](http://hackage.haskell.org/package/lens) and
[`profunctors`](http://hackage.haskell.org/package/profunctors) packages.
["Profunctor Optics: Modular Data Accessors"](https://arxiv.org/abs/1703.10857)
by Matthew Pickering et al, and Oleg's [Glassery](http://oleg.fi/gists/posts/2017-04-18-glassery.html)
were also major inspirations. Both are recommended reads.
If you're new to profunctors, [this post](http://blog.sigfpe.com/2011/07/profunctors-in-haskell.html) is an excellent introduction.



The entailment lattice of profunctor type classes exposes an optics hierarchy:

<div class="text-center">
<img title="optics diagram" src="./optics-hierarchy.svg" />
</div>

This graph is an entailment (i.e. inheritance) graph of optic classes. 
Each color represents a different type class constraint. 
At the bottom of the optical hierarchy rests the humble [semantic editor combinator](http://conal.net/blog/posts/semantic-editor-combinators
) also known as a Setter. 
At the top of the hierarchy we have ‘Iso’, which is restricted only by the `Profunctor` constraint;
imposing additional `Strong` (<span style="color:#000080">blue</span>) constraint we get `Lens`;
adding `Traversing1` (<span style="color:#008000">green</span>) turns a `Lens` into a `Traversal1`.
Other colors are for `Choice` (<span style="color:#800000">red</span>),
`Bicontravariant` (<span style="color:#ff8000">orange</span>),
`Bifunctor` (<span style="color:#8000ff">purple</span>), and
`Mapping` (<span style="color:#808080">gray</span>). There is no color
for `Traversing` as it's (almost) the combination of `Traversing1` and `Choice`.
The `Strong` part of the graph can also be indexed: `IndexedLens`, `IndexedTraversal` etc. 


With the van Laarhoven encoding of optics (i.e. the encoding in [`lens`](http://hackage.haskell.org/package/lens/docs/Control-Lens-Type.html)), 
you get roughly the same hierarchy. 
However the base `Optic` type in the van Laarhoven encoding includes an additional functor, which can lead to complications. 
Among other things, it makes it very difficult to do things like existensialize over type variables and still use the combinators.
Such a need arose during the creation of `profunctor-ref`, which is what led to this library in the first place. 

See the documentation in [`Control.Lens.Type`](http://hackage.haskell.org/package/lens/docs/Control-Lens-Type.html).



For each optic type there is a constructor and characterizing operations, which are analogous to the introduction and elimination rules in logic. For example, for lenses:

```
lens (view l) (set l) ≡ l
      view (lens g s) ≡ g
       set (lens g s) ≡ s
```

Compare that to the local soundness and completeness of conjunction:

```
pair (fst p) (snd p) ≡ p  -- complete
      fst (pair x y) ≡ x  -- sound 1
      snd (pair x y) ≡ y  -- sound 2
```

these laws are captured in property tests in the test folder.




| | `Forget` | `Star` | `Tagged` | `Zipping` |
| --- | --- | --- | --- | --- |
| `Bifunctor`       | no      | no      | **yes** | no      |
| `Bicontravariant` | **yes** | no      | no      | no      |
| `Choice`          | **yes** | **yes** | **yes** | **yes** |
| `Strong`          | **yes** | **yes** | no      | **yes** |
| `Closed`          | **yes** | no      | **yes** | **yes** |
| `Monoidal`        | **yes** | **yes** | **yes** | **yes** |

| Optic | Constructor | Operations | Type class | Profunctor |
| --- | --- | --- | --- | --- |
| [Equality](#equality)                 | `id`, `simple`  |                      |                     | `Identical` |
| [Iso](#iso)                           | `iso`           | `view`, `review`     | `Profunctor`        |             |
| [Prism](#prism)                       | `prism`         | `matching`, `review` | `Choice`            | `Matching`   |
| [Review](#review)                     | `upto`          | `review`             | `Bifunctor`         | `Tagged`    |
| [Getter](#getter)                     | `to`            | `view`               | `Bicontravariant`   |             |
| [Lens](#lens)                         | `lens`          | `view`, `set`        | `Strong`            |             |
| [Affine Traversal](#affine-traversal) | `affine`        | `matching`, `set`    | `Choice`, `Strong`  |             |
| [Traversal1](#traversal1)             | `traversing1`   | `traverse1Of`        | `Traversing1`       | `Star`      |
| [Traversal](#traversal)               | `traversing`    | `traverseOf`         | `Traversing`        | `Star`      |
| [Affine Fold](#fold-fold1-and-affine-fold) | `afolding` | `preview`            |                     | `Preview`   |
| [Fold1](#fold-fold1-and-affine-fold)  | `folding1`      | `foldMap1Of`         |                     | `Forget`    |
| [Fold](#fold-fold1-and-affine-fold)   | `folding`       | `foldMapOf`          |                     | `Forget`    |
| [Setter](#setter)                     | `setting`       | `over`               | `Mapping`           | `(->)`      |


[poptic](https://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/poptics.pdf)

`poptic` builds upon (and is much indebted to) prior work by: Ed Kmett, Russell O’Connor, Twan van Laarhoven, Jeremy Gibbons, Matthew Pickering, Guillaume Boisseau, Oleg Grenrus, Phil Freeman, and many others.

Its purpose is to provide a semantically precise and performant implementation of profunctor-encoded optics, suitable for application development.

Why another optics library? Mainly because for many applications the profunctor encoding of optics is easier to understand and work with than the van Laarhoven encoding. This makes sense for applications, who are both heavy optic users and not worried about non-base dependencies.

The category theory behind profunctor optics is well-described in the following papers:
- [Profunctor Optics: Modular Data Accessors](https://arxiv.org/abs/1703.10857) by Pickering, Gibbons, and Wu
- [What You Needa Know about Yoneda](https://www.cs.ox.ac.uk/jeremy.gibbons/publications/proyo.pdf) by Gibbons and Boisseau 

If you're new to profunctors, [this talk](https://www.youtube.com/watch?v=OJtGECfksds) by Phil Freeman and [this post](http://blog.sigfpe.com/2011/07/profunctors-in-haskell.html) by Dan Piponi are good general introductions. Oleg Grenrus has several blog excellent blog posts (notably [this one](http://oleg.fi/gists/posts/2017-04-18-glassery.html) that provide a synthesis of the Pickering paper for Haskellers.


## Intro

For day-to-day usage there are several distinct components that are helpful to differentiate up front:

- the profunctor type classes (e.g. `Profunctor`, `Strong`, `Choice`, `Traversing`, `Closed` etc)
- the corresponding optic types (e.g. `Lens`, `Prism`, `Affine`, `Traversal`, `Fold` etc), induced by entailment relations between the type classes above (see chart below)
- particular optics (e.g. `_1 :: Strong p => Optic p (a, c) (b, c) a b`), derived from the various profunctor typeclass functions (e.g. `dimap`, `first'`) and often user-supplied
- particular profunctors (e.g. `Star (Pre r) s a`, `Costar (Const Text) [Text] Text`, `Int -> Int`, etc)
- characteristic operators (e.g. `.`, `to`, `view`, `matching`, etc), which induce laws (e.g. get/put laws) and are often derived by passing a particular 'carrier' profunctor specific to that operator through the supplied optic:

```
traverseOf :: Optic (Star f) s t a b -> (a -> f b) -> s -> f t
traverseOf o f = tf where Star tf = o (Star f)
```
- and finally derived operators like `sequenceOf`, which comprise the bulk of the library:

```
sequenceOf :: Applicative f => Traversal s t (f a) a -> s -> f t
sequenceOf t = traverseOf t id
```


The lattice of entailment relations between the various profunctor type classes looks like this:

<div class="text-center">
<img title="optics diagram" src="./optics-hierarchy.svg" />
</div>

Credit to Oleg I think for the original version of this diagram.
Each node in the lattice corresponds to a conjunction of type class constraints on a function of the type `p a b -> p s t`.
For example, at the bottom (top in the diagram) of the hierarchy is an `Over` (or `over` in lens parlance), also known as a [semantic editor combinator](http://conal.net/blog/posts/semantic-editor-combinators).
Overs have the following type 

```
type Over s t a b = forall p. c p => p a b -> p s t
``` 

where the constraint `c` is given by the conjunction of the `Profunctor`, `Strong`, `Choice`, `Traversing`, `Closed`, and `Mapping` type classes.

At the top of the hierarchy is an `Iso`, which is restricted only by the `Profunctor` constraint (designated by the black arrow at the bottom, and suppressed elsewhere for clarity since everything uses it)
Imposing an additional `Strong` (<span style="color:#000080">blue</span> arrows) constraint we get `Lens`,
and adding `Traversing1` (<span style="color:#008000">green</span> arrows) turns a `Lens` into a `Traversal1`.

The other colors denote `Choice` (<span style="color:#800000">red</span>),
`OutPhantom` (<span style="color:#ff8000">orange</span>),
`InPhantom` (<span style="color:#8000ff">purple</span>), and
`Mapping` (<span style="color:#808080">gray</span>). 
Note that there is no arrow for the `Traversing` class, since it is equivalent to the conjunction of `Profunctor`, `Traversing1`, `Strong`, and `Choice`.
The `Strong` (left) side of the graph can also be indexed, leading to `IndexedLens`, `IndexedTraversal` etc. 

Each time we add an additional constraint, the corresponding set of optics gains some additional capabilities at the cost of some generality. 
Consequently a `Fold` can make use of far fewer operators than an `Iso`.

For a more detailed example consider the `review` operator, which is derived from the `Costar (Const c)` profunctor (via `unfoldMapOf`). However `Costar (Const c)` is not an instance of `Mapping` (because its contravariant type paramater is phantom).
It follows then that an `Over s t a b`, which as we noted above is constrained by `Mapping`, will not be compatible with the `review` operator.

Finally note that intra-module imports also follow the entailment DAG. So for example an operator with `Profunctor` and `Choice` constraints will be located in `Data.Profunctor.Optic.Prism` (i.e. in the module corresponding to the conjuction of the constraints). 

## Laws
For each optic there is a 'constructor' and characteristic operators, which are analogous to the introduction and elimination rules in logic. 
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

| Optic | Constructor | Characteristic Operators | Assoc. Constraint | Assoc. Profunctor 
| --- | --- | --- | --- | --- |            
| [PrimView](#view)              | `to`          |                   | `OutPhantom`  | `s -> a`                                 
| [View](#view)                  | `to`          | `view`            |               | `Star (Const a) s a`                     
| [PrimReview](#review)          | `unto`        |                   | `InPhantom`   | `b -> t`               
| [Review](#review)              | `unto`        | `review`          |               | `Costar (Const b) t b` 
| [Iso](#iso)                    | `iso`         | `re`              | `Profunctor`  | `(s -> a, b -> t)`               
| [Grate](#grate)                | `grate`       | `cotraverseOf`    | `Closed`      | `((s -> a) -> b) -> t`
| [Over](#over)                  | `over`        | `mapOf`           | `Mapping`     | `(a -> b) -> s -> t`        
| [Lens](#lens)                  | `lens`        | `view`, `mapOf`   | `Strong`      | `(s -> a, s -> b -> t)`            
| [Prism](#prism)                | `prism`       | `match`, `review` | `Choice`      | `(s -> Either t a, b -> t)`           
| [Affine Traversal](#traversal) | `affine`      | `match`, `mapOf`  |               | `(s -> Either t a, s -> b -> t)`     
| [Traversal1](#traversal)       | `traversing1` | `traverseOf`      | `Traversing1` | `(s -> NonEmpty a, s -> NonEmpty b -> t)`
| [Traversal](#traversal)        | `traversing`  | `traverseOf`      | `Traversing`  | `(s -> [a], s -> [b] -> t)`              
| [Affine Fold](#fold)           | `afolding`    | `preview`         |               | `Star (Pre a) s a`     
| [Fold1](#fold)                 | `folding1`    | `toNelOf`         | `Semigroup r` | `Star (Const r) s a`   
| [Fold](#fold)                  | `folding`     | `toListOf`        | `Monoid r`    | `Star (Const r) s a`   

The laws are captured in property-driven tests in the test folder. Predicates describing the laws are kept along with the constructors so that they can be used to verify downstream optics.




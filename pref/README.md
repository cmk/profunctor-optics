An optic (e.g. one of the types in [`Control.Lens.Type`](http://hackage.haskell.org/package/lens-4.17/docs/Control-Lens-Type.html)) naturally divides into what, for the purposes of this readme, I'll call 'backend' input/outputs (i.e. `s` and `t`, but really any types associated with your resource management layer) and 'frontend' input/outputs (i.e. `a` and `b`, but really any types associated with your domain logic layer).

Now if you use the [profunctor](https://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/poptics.pdf) encoding (e.g. from [`poptic`](https://github.com/cmk/putil/blob/master/poptic/src/Data/Profunctor/Optic/Types.hs#L20)) instead of the [van Laarhoven](https://www.twanvl.nl/blog/haskell/cps-functional-references) one (e.g. from [`lens`](http://hackage.haskell.org/package/lens-4.17/docs/Control-Lens-Type.html#t:Optic)) you gain precise control over data access with [just the one type variable](https://github.com/cmk/putil/blob/master/poptic/src/Data/Profunctor/Optic/Types.hs#L16) representing a constraint. If you then further combine this `c` with the `c` trick from the "Build Systems à la Carte" paper (see [`Task`](https://hackage.haskell.org/package/build-1.0/docs/Build-Task.html#t:Task)) and existentialize over the two 'backend' types, you get the following [type](https://github.com/cmk/putil/blob/master/pref/src/Data/Profunctor/Reference/PRefs.hs):


```
data PRefs c rt rs b a = forall x y . PRefs (Optical c x y a b) !(rs x) !(rt y)
```

that I haven't been able to trace down anywhere and so am provisionally calling a profunctor reference (borrowed from SML's [references](https://www.cs.cmu.edu/~rwh/introsml/core/refs.htm)).  

Profunctor references are basically input / output resources `rs` and `rt`, bound together with a profunctor-encoded optic by existentializing over the `s` and `t` types. 
The effect of existentializing over the backend types is that 'frontend' code can no longer rely on any particular instantiation of inputs or outputs to the component in question, 
be it an [exception](https://github.com/cmk/putil/blob/master/pref/src/Data/Profunctor/Reference/PError.hs)
, [io ref](https://github.com/cmk/putil/blob/master/pref/src/Data/Profunctor/Reference/PIORef.hs)
, [mvar](https://github.com/cmk/putil/blob/master/pref/src/Data/Profunctor/Reference/PMVar.hs)
, [io-stream](https://github.com/cmk/putil/blob/master/pref/src/Data/Profunctor/Reference/PStreams.hs), `TChan`, kinesis stream, logger, etc. 
The result is essentially the same decoupling you get with traditional typeclass-mediated resource management, but without the typeclasses and _with_ all the laws and composability you get from profunctors & arrows (e.g. [`dimap`](http://hackage.haskell.org/package/profunctors-5.3/docs/Data-Profunctor.html#v:dimap), [`first'`](http://hackage.haskell.org/package/profunctors-5.3/docs/Data-Profunctor.html#v:first-39-), [`left'`](http://hackage.haskell.org/package/profunctors-5.3/docs/Data-Profunctor.html#v:left-39-), and so forth).

So for example you can `dimap` them like this:

```
>>> s = ("hi",2) :: (String, Int)
>>> t = ("there!",2) :: (String, Int)
>>> rs <- newIORef s
>>> rt <- newIORef t
>>> o :: PRefs Profunctor IORef IORef (String, Int) (String, Int) = PRefs id rt rs
>>> readPIORefs (dimap id fst o)
"hi"
```
or this:
```
>>> tosnd a = ("bye", a)
>>> o' :: PRefs Profunctor IORef IORef Int String = dimap tosnd fst o
>>> modifyPIORefs o' length >> readIORef rt
("bye",2)
>>> readIORef rs
("hi",2)
```

They also form a category, so they compose:

```
import Control.Category (>>>)

declareIORef "x" [t| (String, Int) |] [e| ("hi!", 2) |]
declareIORef "y" [t| (Int, String) |] [e| (4, "there") |]

swapped :: Iso (a, b) (b', a') (b, a) (a', b')
swapped = iso swap swap

j :: PRefs Profunctor IORef IORef (Int, String) (String, Int) 
j = PRefs swapped y x

i :: PRefs Profunctor IORef IORef (String, Int) (Int, String) 
i = PRefs swapped x y

ji :: PRefs Profunctor IORef IORef (Int, String) (Int, String)
ji = j >>> i
```

Finally there's also a simplified version that contains only one underlying reference:

```
data PRef c rs b a = forall x . PRef  (Optical c x x a b) !(rs x)
```
which is usable for reading / writing / modifying depending on the profunctor constraint `c`.


One goal with this experiment is to try and find a viable alternative to the type-class heavy approaches to resource abstraction (e.g. `MonadFoo`, `HasBar`, `AsBaz` etc) currently prevalent. 
The resulting `HasBar` alternative is [here](https://github.com/cmk/putil/blob/master/pref/src/Data/Profunctor/Reference/PRefs.hs#L106) for the separate read/write case and [here](https://github.com/cmk/putil/blob/master/pref/src/Data/Profunctor/Reference/PRef.hs#L146) for the single reference case:

```
has :: MonadReader r m => c (Star (Const a)) => PRef c ((->) r) b a -> m a
has (PRef o rs) = view o <$> asks rs
```
along with a combinator to cover the common `myfunc :: (HasBar r, HasBippy r, MonadReader r m) => ...` use case:
```
asksBoth :: (MonadReader r m, Applicative m) => (r -> PRef Strong m b1 a1) -> (r -> PRef Strong m b2 a2) -> m (PRef Strong m (b1, b2) (a1, a2))
asksBoth r s = liftA2 (*$*) (asks r) (asks s)
```


This approach applies to more that just the has pattern. For one thing, the fact that we're dealing with profunctors means we can also expose backend resources to users as sum types:
```
asksEither :: (MonadReader r m, Decidable m) => (r -> PRef Choice m b1 a1) -> (r -> PRef Choice m b2 a2) -> m (PRef Choice m (Either b1 b2) (Either a1 a2))
asksEither r s = liftA2 (+$+) (asks r) (asks s)
```

The `*$*` and `+$+` operators above are essentially `***` and `+++` from [`Control.Arrow`](http://hackage.haskell.org/package/base-4.11.1.0/docs/Control-Arrow.html):

```
(*$*) :: Applicative f => PRef Strong f b1 a1 -> PRef Strong f b2 a2 -> PRef Strong f (b1, b2) (a1, a2)
(*$*) (PRef o f) (PRef o' f') = PRef (o *** o') (liftA2 (,) f f')

(+$+) :: Decidable f => PRef Choice f b1 a1 -> PRef Choice f b2 a2 -> PRef Choice f (Either b1 b2) (Either a1 a2)
(+$+) (PRef o f) (PRef o' f') = PRef (o +++ o') (f >+< f')
```
where `(>+<) :: Decidable f => f a -> f b -> f (Either a b)` is a [`contravariant`](http://hackage.haskell.org/package/contravariant-1.5) cousin to `liftA2 (,) :: Applicative f => f a -> f b -> f (a, b)`.


Because the resources are completely abstracted behind `s`, `t`, `rs`, and `rt` (and possibly also constraints on `s` and `t`, still protyping this) we can apply the same functions to essentially any set of operations that you can fit into a `foo m b a = MonadUnliftIO m => (b -> m (), m a)` (which is itself a profunctor).
So for example the `(+$+)` operator I defined above also has a specialization (defined in [`PError`](https://github.com/cmk/putil/blob/master/pref/src/Data/Profunctor/Reference/PError.hs)):

```
(+!+) :: MonadPlus m => PError m Choice a -> PError m Choice b -> PError m Choice (Either a b)
(+!+) (PRef o f) (PRef o' f') = PRef (o +++ o') (f >+< f')
```
which effectivey models your exceptions as a free monoid that can run in two separate interpreters, one on the backend and one on the frontend. See [`catching`](https://github.com/cmk/putil/blob/master/pref/src/Data/Profunctor/Reference/PError.hs#L151).
This is convenient if you like to [keep your error types small](https://www.parsonsmatt.org/2018/11/03/trouble_with_typed_errors.html).

Finally, the `AsBaz` analog I mentioned above is simply:
```
asException :: (MonadIO m, Exception s, Exception a) => Prism' s a -> Error m s -> PError m Choice a
asException o h = PRef o h
```
where, like the actual instantiations of `env` in your typical `AsFoo env` instance, instantiations of the `s` exception are unreachable by users of `PError m Choice a`. Like in the has pattern, any knowledge of the actual resources beyond the `rs` and `rt` types has been completely erased at the type level. The domain logic and resource management sides of your application can be compiled separately, or be maintained by different people using the `PRefs` as the go-between. 


This approach provides a lot of design latitude to the resource management side of your program. For example, you can create one large exception type for the whole application, or integrate a number of smaller exception types & handlers (see `PError`). You can use a single piece of 'fat' state (e.g. an `IORef (Map k v)`) or break out a number of smaller pieces of state (see `PIORef`). You can log to disk or to a Kinesis stream, use Redis or PostGres (or even Redis on the read side and Postgres on the write side) (see `PIORefs` and `PStreams`). The domain code can only see the exposed `a` for reads and `b` for writes. 


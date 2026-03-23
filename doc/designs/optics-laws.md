# Cotraversal0Rep Choice and Closed law analysis

Verification that `Cotraversal0Rep`'s `Choice` and `Closed` instances
are lawful. The always-`Left` return in `left'` is not a bug — it's
an inherent consequence of the CPS encoding.

## Setup

```haskell
newtype Cotraversal0Rep a b s t =
  Cotraversal0Rep { unCotraversal0Rep :: ((s -> t + a) -> b) -> t }

instance Choice (Cotraversal0Rep a b) where
  left' (Cotraversal0Rep stabt) =
    Cotraversal0Rep $ \f ->
      Left $ stabt $ \sta ->
        f $ eassocl . fmap eswap . eassocr . first sta

instance Closed (Cotraversal0Rep a b) where
  closed (Cotraversal0Rep stabt) =
    Cotraversal0Rep $ \f x ->
      stabt $ \sta -> f $ \xs -> first const $ sta (xs x)
```

## Choice: left-unit law

The key law to verify:

```
lmap Left . left' ≡ rmap Left
```

"If we inject into `Left` then apply `left'`, it should be the same
as just mapping `Left` over the output."

### RHS: `rmap Left`

From `dimap`:

```haskell
dimap us tv (Cotraversal0Rep stabt) =
  Cotraversal0Rep $ \f -> tv (stabt $ \sta -> f (first tv . sta . us))
```

So `rmap Left = dimap id Left`:

```haskell
Cotraversal0Rep $ \f -> Left (stabt $ \sta -> f (first Left . sta))
```

where `sta :: s -> t + a` and `first Left :: t + a -> (t + c) + a`.

### LHS: `lmap Left . left'`

First, `left'`:

```haskell
Cotraversal0Rep $ \f ->
  Left $ stabt $ \sta ->
    f $ eassocl . fmap eswap . eassocr . first sta
```

The inner `f :: (s + c -> (t + c) + a) -> b`.

The composed chain `eassocl . fmap eswap . eassocr . first sta`
on input `s + c`:

1. `first sta :: s + c -> (t + a) + c` — applies `sta` to `Left` case
2. `eassocr :: (t + a) + c -> t + (a + c)`
3. `fmap eswap :: t + (a + c) -> t + (c + a)` — swaps inside `Right`
4. `eassocl :: t + (c + a) -> (t + c) + a`

So the composed function is `s + c -> (t + c) + a`. Types check.

Now `lmap Left` on this:

```haskell
Cotraversal0Rep $ \f ->
  Left $ stabt $ \sta ->
    f (eassocl . fmap eswap . eassocr . first sta . Left)
```

Simplifying `eassocl . fmap eswap . eassocr . first sta . Left`
for input `s`:

1. `Left s`
2. `first sta (Left s) = Left (sta s)`
3. If `sta s = Left t`:
   `Left (Left t) → eassocr → Left t → fmap eswap → Left t → eassocl → Left (Left t)`
4. If `sta s = Right a`:
   `Left (Right a) → eassocr → Right (Left a) → fmap eswap → Right (Right a) → eassocl → Right a`

So the chain equals `first Left . sta`:

```haskell
\s -> case sta s of
  Left t  -> Left (Left t)   -- = first Left (Left t)
  Right a -> Right a          -- = first Left (Right a)
```

Therefore the LHS becomes:

```haskell
Cotraversal0Rep $ \f -> Left $ stabt $ \sta -> f (first Left . sta)
```

Which is exactly the RHS. **The left-unit law holds.**

## Why `left'` always returns `Left`

`Cotraversal0Rep a b s t = ((s -> t + a) -> b) -> t` is a CPS type
where `t` is produced by running the continuation. There is no
"stored" `s` value — values of `s` only appear inside the callback.

For `left' :: Cotraversal0Rep a b s t -> Cotraversal0Rep a b (s+c) (t+c)`:
we need to produce `t + c`. Since the CPS can produce `t` but has no
access to any `c` value, `Left t` is the only possibility.

This is analogous to `ColensRep`'s `Closed` instance:

```haskell
closed (ColensRep sabt) = ColensRep $ \xsab x ->
  sabt $ \sa -> xsab $ \xs -> sa (xs x)
```

The `x` argument is only fed into the callback — the structure
always passes through the CPS.

## Closed instance

```haskell
closed (Cotraversal0Rep stabt) =
  Cotraversal0Rep $ \f x ->
    stabt $ \sta -> f $ \xs -> first const $ sta (xs x)
```

Here `sta :: s -> t + a` and `xs :: x -> s`, so `sta (xs x) :: t + a`.
Then `first const :: t + a -> (x -> t) + a` lifts `t` into a constant
function `x -> t`. This correctly adapts the callback for
`closed :: p s t -> p (x -> s) (x -> t)`.

## Intuition

`Cotraversal0Rep` is the dual of `Traversal0Rep` (formerly
`AffineRep`). Just as `Traversal0Rep`'s `Strong` instance wraps extra
context alongside the stored data, `Cotraversal0Rep`'s `Choice`
instance threads extra alternatives through the continuation.

The continuation never produces `Right c` because the CPS structure
only knows how to produce `t`. The `c` path is only reachable when
the adapted callback is invoked with a `Right c` input, and in that
case the callback handles it internally. The outer CPS always wraps
in `Left`.

The always-`Left` pattern in `left'` is the natural consequence of
CPS: the continuation produces a `t`, and wrapping it in `Left` is
the only way to embed it into `t + c`.

## Summary

Both `Choice` and `Closed` instances of `Cotraversal0Rep` are
correctly encoded. The property tests in `Test.Carrier` verify the
left-unit law and the `Closed` identity empirically.

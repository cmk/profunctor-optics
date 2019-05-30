module Data.Profunctor.Optic.Lens (
    module Data.Profunctor.Optic.Lens
  , module Export
) where

import Data.Profunctor.Optic.Prelude
import Data.Profunctor.Optic.Type
import Data.Void (Void, absurd)

import Data.Profunctor.Strong as Export


---------------------------------------------------------------------
-- 'Lens' 
---------------------------------------------------------------------

{- Hedgehog predicates

Lens is the characterization of a Strong profunctor. It identifies 
objects as consisting of a product of two components.

viewUpdate :: Eq s => LensRep s s a a -> s -> Bool
viewUpdate (LensRep v u) s = u ((v s), s) == s

updateView :: Eq a => LensRep s s a a -> a -> s -> Bool
updateView (LensRep v u) a s = v (u (a, s)) == a

updateUpdate :: Eq s => LensRep s s a a -> a -> a -> s -> Bool
updateUpdate (LensRep v u) a1 a2 s = u (a2, (u (a1, s))) == u (a2, s)

lens_complete :: Lens s t a b -> Bool
lens_complete o = tripping o $ lens (view o) (set o)

laws
You get back what you put in:
view l (set l v s)  ≡ v
Putting back what you got doesn't change anything:
set l (view l s) s  ≡ s
Setting twice is the same as setting once:
set l v' (set l v s) ≡ set l v' s

-}

-- lens sa sbt = dimap (sa &&& id) (uncurry . flip $ sbt) . first'
-- lens sa sbt = dimap (id &&& sa) (uncurry sbt) . second'
lens :: (s -> a) -> (s -> b -> t) -> Lens s t a b
lens sa sbt = dimap (id &&& sa) (uncurry sbt) . second'

-- Analogous to (***) from 'Control.Arrow'
--(*|*) :: Lens s t a b -> Lens s' t' a' b' -> Lens (s * s') (t * t') (a * a') (b * b')
(*|*) :: Lens s t a b -> Lens s' t' a' b' -> Lens (s, s') (t, t') (a, a') (b, b')
(*|*) = paired

lensOf
  :: (s -> a)
  -> (s -> b -> t) 
  -> Lens (c, s) (d, t) (c, a) (d, b)
lensOf f g = between runPaired Paired (lens f g)

cloneLens :: ALens s t a b -> Lens s t a b
cloneLens l = withLens l $ \x y p -> lens x y p

withLens :: ALens s t a b -> ((s -> a) -> (s -> b -> t) -> r) -> r
withLens l f = case l (LensRep id $ \_ b -> b) of LensRep x y -> f x y

---------------------------------------------------------------------
-- 
---------------------------------------------------------------------


-- | The `LensRep` profunctor precisely characterizes a 'Lens'.
data LensRep a b s t = LensRep (s -> a) (s -> b -> t)

instance Profunctor (LensRep a b) where

  dimap f g (LensRep sa sbt) = LensRep (sa . f) (\s -> g . sbt (f s))

instance Strong (LensRep a b) where

  first' (LensRep sa sbt) =
    LensRep (\(a, _) -> sa a) (\(s, c) b -> ((sbt s b), c))

  second' (LensRep sa sbt) =
    LensRep (\(_, a) -> sa a) (\(c, s) b -> (c, (sbt s b)))

-- | When you see this as an argument to a function, it expects a 'Lens'.
type ALens s t a b = Optic (LensRep a b) s t a b

type ALens' s a = ALens s s a a

---------------------------------------------------------------------
-- Common lenses 
---------------------------------------------------------------------

-- | There is a `Unit` in everything.
united :: forall a. Lens' a ()
united = lens (const ()) const

-- | There is everything in `Void`.
devoid :: forall a. Lens' Void a
devoid = lens absurd const
